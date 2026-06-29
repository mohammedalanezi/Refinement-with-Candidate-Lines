#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <chrono>
#include <cstdlib>
#include <algorithm>

#include "cadical.hpp"
#include "exhaustive.hpp"

#define COPY_MODE 1 // copy (1) faster than assumption mode (0) since we don't encounter clause poisoning, this is unknown for massively larger templates (e.g. 4) 
#define FULL_DUMP 0 // if we dump irredundant clauses/unit clauses to march_cu
#define MAX_CUBES 0 // maximum cubes we process, infinite when <=0, this is for early termination
#define TRACK_TIME 1 // Track timings, GLOBAL WALL TIME ALWAYS TRACKED

#define CANEARLY 1 // 1 is fastest
#define MINIMIZE 0 // 0 is fastest
#define CANFORGET 1 // 1 is fastest

#define MIN_LINES 5 // 3-5 faster than 6 with no minimzation 

using namespace std; 

// ---------------------------------------------------------------
// Constants
// ---------------------------------------------------------------

#define ORDER_DEFINED
const int order        = 10;
const int latin_squares = 3;

// max variable index for square Q (sq=0): vars 1 ... order^3, sent to march_cu's -m flag so it only branches on Q's variables
const int Q_MAX_VAR = order * order * order;  // = 1000

vector<vector<vector<int>>> tmpl(2);

double init_creation_time = 0.0f;
double total_cube_creation_time = 0.0f;
double total_cube_solve_time = 0.0f;
double total_cube_gen_time = 0.0f;

double total_minimize_setup = 0.0;
double total_minimize_remove = 0.0;

bool cube_solver_created = false;
int cube_count = 0;
long early_blocks = 0;
long early_blocks_total = 0;

CaDiCaL::Solver solver;
ExhaustiveSearchOptions opts;
string g_march_cu_path; // Path to the march_cu binary; set in main() from march_cu_dir.

// Number of free variables march_cu removes before emitting a cube (-r param).
// Increase this to get more cubes (each harder cube). We wait to solve each cube in a couple minutes at most but not too fast where creation/destruction of cadical slows it down.
int CUBE_R_PARAM = 20; // (when we rebuild a solver for each cube) 20 seems to be the fastest time after naive testing of various values between 5 and 50
int CUBE_LIMIT = 0; // Max number of cubes that will be solved
int CUBE_START = 0; // The cube to start solving from

int SAT_SEED = 0; // Seed of the Cubes, <= -1 adds no seed

#include "partial_solution_refinement.cpp"

// ---------------------------------------------------------------
// Variable layout
//
// Squares: 0 = Q  (first parallel class)
//          1 = Z  (second parallel class)
//          2 = P  (auxiliary orthogonality square)
//
// var(sq, r, c, s) encodes: "cell (r,c) of square sq carries symbol s"
// Variables are 1-based and laid out as [sq][r][c][s] in row-major order.
// Total base variables: 3 * 10^3 = 3000.
// ---------------------------------------------------------------
inline int var(int sq, int r, int c, int s) {
	return sq * order * order * order + r  * order * order + c  * order + s  + 1;
}

// ---------------------------------------------------------------
// Template loading
//
// Template file layout (matching unloadTemplate in helpers.py):
//   Lines 0–9   -> Q's template  (template[0][row][col] ∈ {0,1})
//   Line  10    -> blank separator
//   Lines 11–20 -> Z's template  (template[1][row][col] ∈ {0,1})
//
// A '1' in the template means the cell belongs to the "relational"
// (symbol 0–3) partition; '0' means the "non-relational" (4–9) partition.
// ---------------------------------------------------------------
void unloadTemplate(const string& path) {
	ifstream f(path);
	if (!f.is_open()) {
		cerr << "Cannot open template file: " << path << "\n";
		return;
	}
	string line;
	int line_no = 0;
	while (getline(f, line)) {
		while (!line.empty() && (line.back() == '\r' || line.back() == '\n' || line.back() == ' ')) // Strip trailing whitespace / CR
			line.pop_back();

		if (!line.empty()) {
			if (line_no <= 9) {
				tmpl[0].push_back({});
				for (char ch : line)
					tmpl[0].back().push_back(ch - '0');
			} else if (line_no > 10 && line_no <= 20) {
				tmpl[1].push_back({});
				for (char ch : line)
					tmpl[1].back().push_back(ch - '0');
			}
		}
		++line_no;
	}
}

// ---------------------------------------------------------------
// Latin-square encoding (mirrors encodeLatinSquareOld in helpers.py)
//
// For every (x, y) pair three families of at-least-one clauses are added
// together with all pairwise at-most-one (binary exclusion) clauses:
//
//   clause1: cell (x,y) carries at least one symbol        -> {var(sq,x,y,z) | z}
//   clause2: row x uses symbol y in at least one column    -> {var(sq,x,z,y) | z}
//   clause3: col x uses symbol y in at least one row       -> {var(sq,z,x,y) | z}
//
//   AMO  cell: -var(sq,x,y,z) ∨ -var(sq,x,y,w)  (z =/= w)
//   AMO   row: -var(sq,x,z,y) ∨ -var(sq,x,w,y)  (z =/= w)
//   AMO   col: -var(sq,z,x,y) ∨ -var(sq,w,x,y)  (z =/= w)
// ---------------------------------------------------------------
void encodeLatinSquare(CaDiCaL::Solver& solver, int sq) {
    vector<int> clause1(order), clause2(order), clause3(order);

	for (int x = 0; x < order; ++x) {
		for (int y = 0; y < order; ++y) {
			for (int z = 0; z < order; ++z) {
                clause1[z] = var(sq, x, y, z); // cell (x,y) has symbol z
                clause2[z] = var(sq, x, z, y); // row x, col z, symbol y
                clause3[z] = var(sq, z, x, y); // row z, col x, symbol y

				for (int w = z + 1; w < order; ++w) {
					solver.clause({-var(sq, x, y, z), -var(sq, x, y, w)}); // AMO cell
					solver.clause({-var(sq, x, z, y), -var(sq, x, w, y)}); // AMO row
					solver.clause({-var(sq, z, x, y), -var(sq, w, x, y)}); // AMO col
				}
			}
			solver.clause(clause1);
			solver.clause(clause2);
			solver.clause(clause3);
		}
	}
}

// ---------------------------------------------------------------
// Myrvold orthogonality encoding (mirrors encodeMyrvoldOrthogonality
// in helpers.py)
//
// Uses the auxiliary square P (sq=2) to couple Q (sq=0) and Z (sq=1).
// For every i, i', j, k:
//
//   p = P[i'][j][k]   z = Z[i][j][i']   q = Q[i][j][k]
//
//   (z ∧ p) -> q   <=>   -z ∨ -p ∨  q
//   (z ∧ q) -> p   <=>   -z ∨ -q ∨  p
//   (p ∧ q) -> z   <=>   -p ∨ -q ∨  z
// ---------------------------------------------------------------
void encodeMyrvoldOrthogonality(CaDiCaL::Solver& solver) {
	for (int i = 0; i < order; ++i) {
		for (int ip = 0; ip < order; ++ip) {
			for (int j = 0; j < order; ++j) {
				for (int k = 0; k < order; ++k) {
					int p = var(2, ip, j, k);  // P[i'][j][k]
					int q = var(0, i,  j, k);  // Q[i][j][k]
					int z = var(1, i,  j, ip); // Z[i][j][i']

					solver.clause({-z, -p,  q});
					solver.clause({-z, -q,  p});
					solver.clause({-p, -q,  z});
				}
			}
		}
	}
}

// ---------------------------------------------------------------
// Main encoding and solving routine
// ---------------------------------------------------------------
struct FastPolicy { 
	mutable __uint128_t sym_points[order] 	= { 0 };
	mutable int sym_cnt[order] 				= { 0 }; 	// popcount of each mask
	mutable int sym_A_idx[order] 			= { -1 }; 	// index in cand_hash_A, or -1 if not complete
	mutable __uint128_t cached_union_B 		= 0;		// cached OR of all surviving B masks
	mutable bool union_B_valid 				= false;    // cache validity flag
	mutable int line_count 					= 0;
	
	explicit operator bool() const { return true; }

	void notify_assignment(int var, int lit) const {
		if (var > order * order * order || lit < 0) return; // only sq=0, only pos lits and unassignments

		const VarInfo& vi = var_lookup[var];
		int point = vi.r * order + vi.c + 1; // 1‑based
		int s     = vi.s;
		__uint128_t bit = (__uint128_t)1 << (point - 1); // bit 0...(order*order-1)
		
		bool was_complete = (sym_cnt[s] == order);

		if (lit > 0) { // assign: set bit if not already set
			if (!(sym_points[s] & bit)) {
				sym_points[s] |= bit;
				++sym_cnt[s];
			}
		} else if (lit == 0) { // retract: clear bit if set
			if (sym_points[s] & bit) {
				sym_points[s] &= ~bit;
				--sym_cnt[s];
			}
		}

		bool now_complete = (sym_cnt[s] == order);

		if (now_complete && !was_complete) {
			auto it = cand_hash_A.find(sym_points[s]);
			if(it != cand_hash_A.end()) {
				++line_count;
				sym_A_idx[s] = it->second;
			} else 
				sym_A_idx[s] = -1;
			union_B_valid = false;  
		} else if (!now_complete && was_complete) {
			if(sym_A_idx[s] != -1)
				--line_count;
			sym_A_idx[s] = -1;
			union_B_valid = false;
		}
	}
	static constexpr bool notifyAssignment = true;

	bool operator()(const std::vector<int>& solution) const {
		if(line_count == 10)
			return solve_partial_solution(sym_A_idx);
		return true;
	}

	void reset() const {
		memset(sym_points, 0, sizeof(sym_points));
		memset(sym_cnt, 0, sizeof(sym_cnt));
		memset(sym_A_idx, -1, sizeof(sym_A_idx));
		cached_union_B = 0;
		union_B_valid = false;
	}

	FastPolicy() { reset(); }

#if CANEARLY == 1 || MINIMIZE == 1
	bool is_partial_solution(const std::vector<int>& pos_vars) const { 
		if (line_count <= 0) return false; // too early to check
		
		if (!union_B_valid) {
			cached_union_B = 0;
			check_partial_solution_covering(sym_A_idx, cached_union_B);
			union_B_valid = true;
		}
		return cached_union_B == all_points_mask;
	}

	bool should_early() const {
		#if CANEARLY == 1
		return line_count >= MIN_LINES;
		#else
		return false;
		#endif
	}

	#if MINIMIZE == 1 // TODO: fix: covering checks that are a result of this function end up being attributed to early blocking
	void minimize(std::vector<int>& clause) const {
	#if TRACK_TIME
		auto t_start = chrono::steady_clock::now();
	#endif

		constexpr int MAX_VAR = 1 + order * order * order;
		static thread_local bool in_clause[MAX_VAR] = {};

		for (int lit : clause) in_clause[-lit] = true;

		// Collect active symbols (A-lines that are fully determined)
		static int active_sym[order];
		static const uint64_t* row_ptr[order];
		int n_active = 0;
		for (int s = 0; s < order; ++s)
			if (sym_A_idx[s] >= 0)
				active_sym[n_active++] = s;

		if (n_active == 0) {
			int out = 0;
			for (int lit : clause) {
				if (in_clause[-lit]) {
					clause[out++] = lit;
					in_clause[-lit] = false;
				}
			}
			clause.resize(out);
			return;
		}
		
		// sort by row index so later loops access intersects_once_BA sequentially, improves cache locality & prefetching
		std::sort(active_sym, active_sym + n_active, [this](int a, int b) { return sym_A_idx[a] < sym_A_idx[b]; }); 

		// Stack-allocated prefix & suffix AND products
		static const int words = rows_B; // number of 64‑bit words per A‑line
        constexpr int MAX_ROWS_B = 256; // covers up to 16384 B-lines
		static const int last_word_bits = count_B % 64;
		static const uint64_t last_word_mask = last_word_bits ? (1ULL << last_word_bits) - 1 : ~0ULL; // this is needed to ensure that suffix and prefix don't AND to have bits in "out-of-bounds" areas
    	alignas(64) static thread_local uint64_t suffix[(order + 1) * MAX_ROWS_B];
		
        // Build suffix products
    	memset(suffix + n_active * words, 0xFF, words * sizeof(uint64_t));
		suffix[n_active * words + words - 1] = last_word_mask;
		const uint64_t* next_row = intersects_once_BA + (long long)sym_A_idx[active_sym[n_active - 1]] * words;
		__builtin_prefetch(next_row, 0, 3);
        for (int i = n_active - 1; i >= 0; --i) {
            const uint64_t* __restrict row = next_row;
			row_ptr[i] = row;
			if (i - 1 >= 0) {
				next_row = intersects_once_BA + (long long)sym_A_idx[active_sym[i-1]] * words;
				__builtin_prefetch(next_row, 0, 3);
			}
            uint64_t*       __restrict dst = suffix + i * words;
            const uint64_t* __restrict src = suffix + (i + 1) * words;
            for (int w = 0; w < words; ++w)
                dst[w] = src[w] & row[w];
        }
			
		// Running prefix and redundancy check 
		alignas(64) static thread_local uint64_t running_prefix[MAX_ROWS_B];
		memset(running_prefix, 0xFF, words * sizeof(uint64_t));
		running_prefix[words - 1] = last_word_mask;

	#if TRACK_TIME
		double setup_time = chrono::duration<double>(chrono::steady_clock::now() - t_start).count();
		total_minimize_setup += setup_time;
	#endif

		constexpr int cutoff = 3;
		int number_removed = 0;

        // Check each symbol for redundancy (can the remaining symbols still cover?)
		for (int i = 0; i < n_active; ++i) {
			int s = active_sym[i];
			const uint64_t* right = suffix + (i + 1) * words;

			__uint128_t union_mask = 0;
			bool covers = false;
			bool done = false;

			for (int w = 0; w < words && !done; ++w) {
				uint64_t word = running_prefix[w] & right[w];
				while (word) {
					int bit = __builtin_ctzll(word);
					int idx = w * 64 + bit;
					//if (__builtin_expect(idx >= count_B, 0)) { done = true; break; }
					union_mask |= cand_masks_B[idx];
					if (union_mask == all_points_mask) { covers = true; done = true; break; }
					word &= word - 1;
				}
			}

			if (!covers) { // Remove negated literals of symbol s
				uint64_t lo = (uint64_t)sym_points[s];
				uint64_t hi = (uint64_t)(sym_points[s] >> 64);
				while (lo) { int b = __builtin_ctzll(lo); in_clause[b * order + s + 1] = false; lo &= lo - 1; }
				while (hi) { int b = __builtin_ctzll(hi); in_clause[(b + 64) * order + s + 1] = false; hi &= hi - 1; }
				++number_removed;
				if (number_removed >= cutoff) break;
			} else {
				const uint64_t* row = row_ptr[i];
				for (int w = 0; w < words; ++w)
					running_prefix[w] &= row[w];
			}
		}

        // Rebuild clause from surviving marks
        int out = 0;
        for (int lit : clause) if (in_clause[-lit]) { clause[out++] = lit; in_clause[-lit] = false; }
        clause.resize(out);

	#if TRACK_TIME
		double remove_time = chrono::duration<double>(chrono::steady_clock::now() - t_start).count() - setup_time;
		total_minimize_remove += remove_time;
	#endif
	}
	static constexpr bool minimizeClause = true;
	#else
	static constexpr bool minimizeClause = false;
	#endif
	static constexpr bool earlyClause = true;
#else
	static constexpr bool earlyClause = false;
	static constexpr bool minimizeClause = false;
#endif
}; 

// ---------------------------------------------------------------
// Builds the full formula into 'solver'. 
// Returns the next free auxiliary variable index.
// ---------------------------------------------------------------
int buildFormula(CaDiCaL::Solver& solver, const vector<vector<vector<int>>>& tmpl) {
	// ---- Declare base variables (3 squares * order^3 each) ----
	int total_base_vars = latin_squares * order * order * order;
	int next_aux = total_base_vars + 1;
	
	solver.declare_more_variables(total_base_vars);

	// ---- Latin-square constraints ----
	for (int sq = 0; sq < latin_squares; ++sq)
		encodeLatinSquare(solver, sq);

	// ---- Orthogonality constraints ----
	encodeMyrvoldOrthogonality(solver);

	// ---- Symmetry breaking (from template, row 0 only) ----
	for (int par_class = 0; par_class < 2; ++par_class) {
		int sq = par_class; // Q=0, Z=1
		int relational_ctr    = 0;
		int nonrelational_ctr = 4;
		for (int col = 0; col < order; ++col) {
			if (tmpl[par_class][0][col] == 1) {
				// Unit clause: row 0, col, relationalCounter-th relational symbol
				solver.clause({var(sq, 0, col, relational_ctr)});
				++relational_ctr;
			} else {
				solver.clause({var(sq, 0, col, nonrelational_ctr)});
				++nonrelational_ctr;
			}
		}
	}

	// ---- Gill encoding (parity constraint) ----
	for (int i = 0; i < order; ++i) {
		int ri = (i < 4) ? 1 : 0;
		for (int j = 0; j < order; ++j) {
			int rj = (j < 4) ? 1 : 0;
			for (int s = 0; s < order; ++s) {
				int rs = (s < 4) ? 1 : 0;
				for (int t = 0; t < order; ++t) {
					int rt = (t < 4) ? 1 : 0;
					if ((ri + rj + rs + rt) % 2 == 1)
						solver.clause({-var(0, i, j, s), -var(1, i, j, t)});
				}
			}
		}
	}

	// ---- Template restrictions ----
	for (int par_class = 0; par_class < 2; ++par_class) {
		int sq = par_class;
		for (int row = 0; row < (int)tmpl[par_class].size(); ++row) {
			for (int col = 0; col < (int)tmpl[par_class][row].size(); ++col) {
				if (tmpl[par_class][row][col] == 1) {
					for (int s = 4; s < order; ++s)
						solver.clause({-var(sq, row, col, s)});
				} else {
					for (int s = 0; s < 4; ++s)
						solver.clause({-var(sq, row, col, s)});
				}
			}
		}
	}

	return next_aux;
}

// ---------------------------------------------------------------
// Cube generation
// ---------------------------------------------------------------
static vector<vector<int>> parseCubesFile(const string& path) { // Parses an .icnf cubes file produced by march_cu. Each cube line starts with 'a', contains space-separated literals, ends with 0
	vector<vector<int>> cubes;
	ifstream f(path);
	if (!f.is_open()) {
		cerr << "Cannot open cubes file: " << path << "\n";
		return cubes;
	}
	string line;
	while (getline(f, line)) {
		if (line.empty() || line[0] != 'a') continue;
		istringstream ss(line.substr(2));
		vector<int> cube;
		int lit;
		while (ss >> lit && lit != 0)
			cube.push_back(lit);
		cubes.push_back(cube);
	}
	return cubes;
}

// Generates cubes by:
//   1. Writing the formula to a temporary DIMACS .cnf file
//   2. Shelling out to march_cu with:
//        -r CUBE_R_PARAM   (stop once this many free vars have been removed)
//        -m Q_MAX_VAR      (only branch on square Q's variables, i.e. vars 1-1000, so every cube fixes a distinct partial assignment of Q
//                           and refinement sees no duplicate work across cubes)
//   3. Parsing the resulting .icnf file
//
// Temp files are written alongside the template in parent_dir and are
// named by template_id so parallel array jobs don't collide.
vector<vector<int>> generateCubes(const vector<vector<vector<int>>>& tmpl, const string& parent_dir, int template_id) {
#if TRACK_TIME
	auto t0 = chrono::steady_clock::now();
#endif

	string cnf_path   = parent_dir + "tmp_t" + to_string(template_id) + ".cnf";
	string cubes_path = parent_dir + "tmp_t" + to_string(template_id) + "_cubes.icnf";

	// Step 1: build a temporary solver just to dump the DIMACS file
	cout << "  Writing CNF to: " << cnf_path << "\n";
	{
		CaDiCaL::Solver dumper; // TODO: could copy instead?
		dumper.set("inprocessing", 0);
		dumper.set("factor",       0);
		buildFormula(dumper, tmpl);
	#if FULL_DUMP == 1
		int stdout_save = dup(fileno(stdout));
		freopen(cnf_path.c_str(), "w", stdout);
		dumper.dump_cnf();
		fflush(stdout);
		dup2(stdout_save, fileno(stdout));
		close(stdout_save);
	#else
		dumper.write_dimacs(cnf_path.c_str());
	#endif
	}

	// Step 2: shell out to march_cu
	//   -r CUBE_R_PARAM : stop after removing this many free variables
	//   -m Q_MAX_VAR    : only branch on vars <= 1000 (square Q)
	//   -l CUBE_LIMIT 	 : combine cubes up to a maximum amount
	//   -o cubes_path   : write cubes here
	ostringstream cmd;
	cmd << g_march_cu_path
		<< " " << cnf_path
		<< " -r " << CUBE_R_PARAM
		<< " -m " << Q_MAX_VAR;
	if (CUBE_LIMIT > 0)
		cmd << " -l " << CUBE_LIMIT;
	cmd << " -o " << cubes_path;

	cout << "  Running: " << cmd.str() << "\n";

	int ret = system(cmd.str().c_str());
#if TRACK_TIME
	double elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
#endif

	if (ret != 0) {
		cerr << "march_cu failed with exit code " << ret << "\n";
		return {};
	}
#if TRACK_TIME
	cout << "  Cubing time: " << elapsed << "s\n";
	total_cube_gen_time = elapsed;
#endif

	// Step 3: parse the .icnf output
	auto cubes = parseCubesFile(cubes_path);
	cout << "  Cubes generated: " << cubes.size() << "\n";
	cube_count = cubes.size();
	return cubes;
}

// ---------------------------------------------------------------
// Solves a single cube: reuses central solver, adds cube as assumption literals, then runs the exhaustive enumeration.
// ---------------------------------------------------------------
#if COPY_MODE == 0
long long solveOneCube(const vector<vector<vector<int>>>& tmpl, const vector<int>& cube, const int& cube_index, ExhaustiveSearch<FastPolicy>& propagator) {
#if TRACK_TIME
	auto t0 = chrono::steady_clock::now();
#endif

	propagator.set_assumptions(cube);
	for (int lit : cube)
		solver.assume(lit);

#if TRACK_TIME
	double create_elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	total_cube_creation_time += create_elapsed;

	t0 = chrono::steady_clock::now();
#endif
	int result = solver.solve();
	solver.simplify();

#if TRACK_TIME
	double solve_elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	total_cube_solve_time += solve_elapsed;
#else
	static double solve_elapsed = -1.0;
#endif

	long long count = propagator.get_solution_count();
	cout << "Cube " << cube_index << "(" << cube.size() << "): " << count << " partial solutions, took " << solve_elapsed << "/" << total_cube_solve_time << "s (" << create_elapsed << "/" << total_cube_creation_time <<"s)" << endl;
	cout << "	Early clauses: " << propagator.get_early_blocking_count() << "/" << propagator.get_attempt_early_blocking_count() << "(" << get_refinement_count() << ")" << endl;

	early_blocks += propagator.get_early_blocking_count();
	early_blocks_total += propagator.get_attempt_early_blocking_count();

	return count;
}
#else
long long solveOneCube(const vector<vector<vector<int>>>& tmpl, const vector<int>& cube, const int& cube_index, ExhaustiveSearch<FastPolicy>& propagator) {
#if TRACK_TIME
	auto t0 = chrono::steady_clock::now();
#endif

	CaDiCaL::Solver copy;
	solver.copy(copy);
	for (int lit : cube)
		copy.clause(lit);

	ExhaustiveSearch<FastPolicy> propagator_(&copy, opts, FastPolicy());

#if TRACK_TIME
	double create_elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	total_cube_creation_time += create_elapsed;

	t0 = chrono::steady_clock::now();
#else
	static double create_elapsed = -1.0;
#endif

	copy.solve();

#if TRACK_TIME
	double solve_elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	total_cube_solve_time += solve_elapsed;
#else
	static double solve_elapsed = -1.0;
#endif

	long long count = propagator_.get_solution_count();
	cout << "Cube " << cube_index << "(" << cube.size() << "): " << count << " partial solutions, took " << solve_elapsed << "/" << total_cube_solve_time << "s (" << create_elapsed << "/" << total_cube_creation_time <<"s)" << endl;
	cout << "	Early clauses: " << propagator_.get_early_blocking_count() << "/" << propagator_.get_attempt_early_blocking_count() << "(" << get_refinement_count() << ", " << get_skipped_count() << ")" << endl;

	early_blocks += propagator_.get_early_blocking_count();
	early_blocks_total += propagator_.get_attempt_early_blocking_count();

	return count;
}
#endif

// ---------------------------------------------------------------
// Runs the entire encoding process from creating the solver to generating to cubes, then finishing by solving them all.
// ---------------------------------------------------------------
long long runEncoding(const string& template_path, int template_id, int observed_syms_A, bool can_forget) {
	auto timer = chrono::steady_clock::now();
	cout << "Running Encoding:\n";

	cout << "	Generating Cubes: march_cu (path=" << g_march_cu_path << ", -r=" << CUBE_R_PARAM << ", -m=" << Q_MAX_VAR << " [Q vars only]";
	if (CUBE_LIMIT > 0)
		cout << ", -l=" << CUBE_LIMIT;
	cout << ")\n";

	// --- Cubing phase ---
	string parent_dir = "./";
	vector<vector<int>> cubes = generateCubes(tmpl, parent_dir, template_id);
	if (cubes.empty()) {
		cout << "No cubes generated (formula UNSAT during cubing or march_cu error).\n";
		return 0;
	}

	cout << "	Creating SAT Instance:\n";
	solver.set("factor",       0);
	solver.set("factorcheck",  0);
	solver.set("inprocessing", 0);
	solver.set("report",       0);
	solver.set("seed", SAT_SEED);
	buildFormula(solver, tmpl);

	vector<int> observed;
	observed.reserve(observed_syms_A * order * order);
	for (int s = 0; s < observed_syms_A; ++s)
		for (int r = 0; r < order; ++r)
			for (int c = 0; c < order; ++c)
				observed.push_back(var(0, r, c, s));
				
	opts.to_observe = observed;
	opts.only_neg   = true;
	opts.can_forget = can_forget;

	FastPolicy proc = FastPolicy();
	ExhaustiveSearch<FastPolicy> propagator(&solver, opts, proc); // TODO: both not needed when COPY_MODE == 1?

	init_creation_time = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	
	// --- Conquer phase (sequential for now; trivial to parallelise later) ---
	long long total = 0;
	int interval = max(1, min(2000, (int)cubes.size()/10));
	auto wall_start = chrono::steady_clock::now();

	int cube_amount = cubes.size();
#if MAX_CUBES > 0
	if(cubes.size() > MAX_CUBES)
		cube_amount = MAX_CUBES;
#endif

	cout << "	Solving Cubes:" << endl;
	for (int i = CUBE_START; i < cube_amount; ++i) {
		total += solveOneCube(tmpl, cubes[i], i, propagator);
		if(i % interval == 0)
			cout << i+1 << "/" << cubes.size() << ": average solve: " << total_cube_solve_time/(i + 1) << "s, average create: " << total_cube_creation_time/(i + 1) << "s, ETA: " << cubes.size() * (total_cube_solve_time/(i + 1) + total_cube_creation_time/(i + 1)) << "s" << endl;
	}

	double total_elapsed = chrono::duration<double>(chrono::steady_clock::now() - wall_start).count();

	cout << "\nTotal wall time: " << total_elapsed << "s\n";
	cout << "Partial Solutions: " << total << "\n";

	return total;
}

// ---------------------------------------------------------------
// Main
// ---------------------------------------------------------------
int main(int argc, char* argv[]) {
	if (argc < 2) {
		cerr << "Usage: " << argv[0] << " <template_id> (# of free vars to remove) (starting cube) (seed) (maximum # of cubes)\n";
		return 1;
	}

	// TODO: read in the template as a binary file, 200 bits each template (100 per square)
	// first i need to edit my template finding code to output in a single binary file

	int template_id     = atoi(argv[1]) + 1; 
	int observed_syms_A = 10;
	if (argc > 2)
		CUBE_R_PARAM = atoi(argv[2]);
	if (argc > 3)
		CUBE_START = atoi(argv[3]);
	if (argc > 4)
		SAT_SEED = atoi(argv[4]);
	if (argc > 5)
		CUBE_LIMIT = atoi(argv[5]);

	string parent_dir    = "../";
	string template_path = parent_dir + "refinements and candidate lines/templates/" + to_string(template_id) + "-template.txt";

	// TODO: On the cluster, use the full absolute path, e.g.: g_march_cu_path = string(getenv("HOME")) + "/CnC-master/march_cu";
	string march_cu_dir  = "../CnC-master/march_cu";
	g_march_cu_path      = march_cu_dir + "/march_cu";

#if COPY_MODE == 1
	cout << "== Copy Model, each cube are turned into literals into their own solver copied from a base solver, no learned clauses transfer over. ==\n";
#else
	cout << "== Assumption Model, each cube are turned into assumptions into a single shared solver, learned clauses transfer over. ==\n";
#endif

	cout << "=== Finding all partial solutions for template " << (template_id - 1) << " ===\n";
	cout << "observed_syms_A        : " << observed_syms_A        << "\n";
	cout << "r_parameter            : " << CUBE_R_PARAM << "\n";
	cout << "starting from cube     : " << CUBE_START << "\n";
	cout << "will early block       : " << CANEARLY << "\n";
	if(CANEARLY > 0) 
		cout << "   minimum lines       : " << MIN_LINES << "\n";
	cout << "will minimize          : " << MINIMIZE << "\n";
	cout << "can forget             : " << CANFORGET << "\n";
	if(SAT_SEED >= 0)
		cout << "sat_seed               : " << SAT_SEED << "\n";
	if(CUBE_LIMIT > 0)
		cout << "cube_limit             : " << CUBE_LIMIT << "\n";

	if (observed_syms_A > 10) {
		cerr << "Too many symbols observed; at most 10 per square.\n";
		return 1;
	}
	if (observed_syms_A <= 0) {
		cerr << "At least one symbol transversal must be observed in either square.\n";
		return 1;
	}
	
	cout << "	Loading template from: " << template_path << "\n";
	unloadTemplate(template_path);
	if (tmpl[0].empty() || tmpl[1].empty()) {
		cerr << "Failed to load a valid template.\n";
		return -1;
	}

	setup(tmpl);

	long long sol_count = runEncoding(template_path, template_id, observed_syms_A, CANFORGET);

	cout << "\n=== FINAL RESULTS FOR TEMPLATE " << (template_id - 1) << " ===\n";
	cout << "Total partial solutions found: " << sol_count << "\n";
	cout << "Total refinements found: " << get_refinement_count() << "\n";
	cout << "Total early blocking attempts: " << early_blocks << "/" << early_blocks_total << "\n";
	cout << "Total cubes: " << cube_count << "\n";

	print_substep_timings_log(init_creation_time, 
		total_minimize_setup, total_minimize_remove,
		total_cube_gen_time, total_cube_creation_time, total_cube_solve_time);

	return 0;
}

/*
TODO: figure out a way to print CPU times, all of these are WALL times (CaDiCaL::Terminator or expose solver->internal somehow? i think its private so id need to expose it again)

TODO: *summary python script, takes in log Id and number of logs, the gets median, average and mode of the logs
	A log is simply a txt file of the results

TODO: run compute canada
	A) need to be able to get all templates individually on compute canada
	B) need to be able to refine templates into candidate lines individually on compute canada
*/