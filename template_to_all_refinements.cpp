
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <span>
#include <string>
#include <chrono>
#include <cstdlib>
#include <algorithm>

#include "cadical.hpp"
#include "exhaustive.hpp"

#define MULTI_THREADING 0 // if I wanna add multi threading to substep then i need a worker and pool system
#define COPY_MODE 1 // copy (1) faster than assumption mode (0) since we don't encounter clause poisoning, this is unknown for massively larger templates (e.g. 4) 
#define FULL_DUMP 0 // if we dump irredundant clauses/unit clauses to march_cu
#define MAX_CUBES 0 // maximum cubes we process, infinite when <=0 (11), this is for early termination

#define CANEARLY 0
#define MINIMIZE 0

using namespace std; 

// ---------------------------------------------------------------
// Constants
// ---------------------------------------------------------------

#define ORDER_DEFINED
const int order        = 10;
const int latin_squares = 3;

// max variable index for square Q (sq=0): vars 1 ... order^3, sent to march_cu's -m flag so it only branches on Q's variables
const int Q_MAX_VAR = order * order * order;  // = 1000

double init_creation_time = 0.0f;
double total_cube_creation_time = 0.0f;
double total_cube_solve_time = 0.0f;
double total_cube_gen_time = 0.0f;

double total_minimize_convert = 0.0;
double total_minimize_cleanup = 0.0;
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

#include "libexact_partial_solution_refinement.cpp"

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

vector<vector<vector<int>>> unloadTemplate(const string& path) {
	vector<vector<vector<int>>> tmpl(2);
	ifstream f(path);
	if (!f.is_open()) {
		cerr << "Cannot open template file: " << path << "\n";
		return tmpl;
	}
	string line;
	int line_no = 0;
	while (getline(f, line)) {
		// Strip trailing whitespace / CR
		while (!line.empty() && (line.back() == '\r' || line.back() == '\n' || line.back() == ' '))
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
	return tmpl;
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
	for (int x = 0; x < order; ++x) {
		for (int y = 0; y < order; ++y) {
			vector<int> clause1, clause2, clause3;
			for (int z = 0; z < order; ++z) {
				clause1.push_back(var(sq, x, y, z)); // cell (x,y) has symbol z
				clause2.push_back(var(sq, x, z, y)); // row x, col z, symbol y
				clause3.push_back(var(sq, z, x, y)); // row z, col x, symbol y

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
	mutable int sym_cnt[order] 				= { 0 }; // popcount of each mask
	mutable int sym_A_idx[order] 			= { -1 }; // index in cand_hash_A, or -1 if not complete
	mutable __uint128_t cached_union_B 		= 0;// cached OR of all surviving B masks
	mutable bool union_B_valid 				= false;    // cache validity flag
	mutable int line_count 					= 0;
	
	explicit operator bool() const { return true; }

	void notify_assignment(int var, int lit) const {
		if (var > order * order * order || lit < 0) // only sq=0, only pos lits and unassignments
			return;

		const VarInfo& vi = var_lookup[var];
		if (vi.sq != 0) return; // only square Q

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
			sym_A_idx[s] = (it != cand_hash_A.end()) ? it->second : -1;
			union_B_valid = false;  
			line_count++;
		} else if (!now_complete && was_complete) {
			sym_A_idx[s] = -1;
			union_B_valid = false;
			line_count--;
		}
	}
	static constexpr bool notifyAssignment = true;
	bool operator()(const std::vector<int>& solution) const {
		return solve_partial_solution(sym_A_idx);
	}

	void reset() const {
		cout << "Reset\n";
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
			getIntersectingBCovering(sym_A_idx, cached_union_B);
			union_B_valid = true;
		}
		return cached_union_B == all_points_mask;
	}

	bool should_early() const {
		#if CANEARLY == 1
		return line_count > 5;
		#else
		return false;
		#endif
	}

	#if MINIMIZE == 1
	void minimize(std::vector<int>& clause) const {
		int local_sym_A_idx[order];
		memcpy(local_sym_A_idx,  sym_A_idx,  sizeof(sym_A_idx));

		std::unordered_set<int> clause_set(clause.begin(), clause.end());

		auto erase_sym_lits = [&](int s, __uint128_t mask) {
			uint64_t lo = (uint64_t)mask;
			uint64_t hi = (uint64_t)(mask >> 64);
			while (lo) { int k = __builtin_ctzll(lo); clause_set.erase(-var(0, k / order, k % order, s)); lo &= lo - 1; }
			while (hi) { int k = __builtin_ctzll(hi); int kk = k + 64; clause_set.erase(-var(0, kk / order, kk % order, s)); hi &= hi - 1; }
		};

		for (int s = 0; s < order; ++s)
			if (local_sym_A_idx[s] > 0) {
				int saved_index = local_sym_A_idx[s];
				local_sym_A_idx[s] = -1;

				bool covers = check_partial_solution_covering(local_sym_A_idx);
				if (covers) {
					local_sym_A_idx[s] = saved_index;
				} else { 
					erase_sym_lits(s, sym_points[s]);
				}
			}
		clause.assign(clause_set.begin(), clause_set.end());
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
	// ---- Declare base variables (3 squares × order^3 each) ----
	int total_base_vars = latin_squares * order * order * order;
	solver.declare_more_variables(total_base_vars);

	// Auxiliary variable counter (for common-transversal section)
	int next_aux = total_base_vars + 1;
	auto new_var_fn = [&]() -> int {
		solver.declare_one_more_variable();
		return next_aux++;
	};

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

// Parses an .icnf cubes file produced by march_cu. Each cube line starts with 'a', contains space-separated literals, ends with 0.
static vector<vector<int>> parseCubesFile(const string& path) {
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
//                           and libexact sees no duplicate work across cubes)
//   3. Parsing the resulting .icnf file
//
// Temp files are written alongside the template in parent_dir and are
// named by template_id so parallel array jobs don't collide.
vector<vector<int>> generateCubes(const vector<vector<vector<int>>>& tmpl, const string& parent_dir, int template_id, int /*cube_depth_unused*/) {
	auto t0 = chrono::steady_clock::now();

	string cnf_path   = parent_dir + "tmp_t" + to_string(template_id) + ".cnf";
	string cubes_path = parent_dir + "tmp_t" + to_string(template_id) + "_cubes.icnf";

	// Step 1: build a temporary solver just to dump the DIMACS file
	cout << "  Writing CNF to: " << cnf_path << "\n";
	{
		CaDiCaL::Solver dumper;
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
	double elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();

	if (ret != 0) {
		cerr << "march_cu failed with exit code " << ret << "\n";
		return {};
	}
	cout << "  Cubing time: " << elapsed << "s\n";
	total_cube_gen_time = elapsed;

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
long long solveOneCube(const vector<vector<vector<int>>>& tmpl, const vector<int>& cube,
						const int& cube_index, ExhaustiveSearch<FastPolicy>& propagator) {
	auto t0 = chrono::steady_clock::now();

	propagator.set_assumptions(cube);
	for (int lit : cube)
		solver.assume(lit);

	double create_elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	total_cube_creation_time += create_elapsed;

	t0 = chrono::steady_clock::now();
	int result = solver.solve();
	solver.simplify();

	double solve_elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	total_cube_solve_time += solve_elapsed;

	long long count = propagator.get_solution_count();
	cout << "Cube " << cube_index << "(" << cube.size() << "): " << count << " partial solutions, took " << solve_elapsed << "/" << total_cube_solve_time << "s (" << create_elapsed << "/" << total_cube_creation_time <<"s)" << endl;
	cout << "	Early clauses: " << propagator.get_early_blocking_count() << "/" << propagator.get_attempt_early_blocking_count() << "(" << get_refinement_count() << ")" << endl;

	early_blocks += propagator.get_early_blocking_count();
	early_blocks_total += propagator.get_attempt_early_blocking_count();

	return count;
}
#else
long long solveOneCube(const vector<vector<vector<int>>>& tmpl, const vector<int>& cube,
						const int& cube_index, ExhaustiveSearch<FastPolicy>& propagator) {
	auto t0 = chrono::steady_clock::now();

	CaDiCaL::Solver copy;
	solver.copy(copy);
	for (int lit : cube)
		copy.clause(lit);

	ExhaustiveSearch<FastPolicy> propagator_(&copy, opts, FastPolicy());

	double create_elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	total_cube_creation_time += create_elapsed;

	t0 = chrono::steady_clock::now();
	int result = copy.solve();

	double solve_elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	total_cube_solve_time += solve_elapsed;

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
long long runEncoding(const string& template_path, int template_id,
					  int observed_syms_A, bool can_forget, int cube_depth = 8) {
	auto timer = chrono::steady_clock::now();
	cout << "Running Encoding:\n";

	cout << "	Loading template from: " << template_path << "\n";
	auto tmpl = unloadTemplate(template_path);
	if (tmpl[0].empty() || tmpl[1].empty()) {
		cerr << "Failed to load a valid template.\n";
		return -1;
	}

	cout << "	Generating Cubes: march_cu (path=" << g_march_cu_path << ", -r=" << CUBE_R_PARAM << ", -m=" << Q_MAX_VAR << " [Q vars only]";
	if (CUBE_LIMIT > 0)
		cout << ", -l=" << CUBE_LIMIT;
	cout << ")\n";

	// --- Cubing phase ---
	string parent_dir = "./";

	vector<vector<int>> cubes = generateCubes(tmpl, parent_dir, template_id, cube_depth);
	if (cubes.empty()) {
		cout << "No cubes generated (formula UNSAT during cubing or march_cu error).\n";
		return 0;
	}

	cout << "	Creating SAT Instance:\n";
	solver.set("factor",       0);
	solver.set("factorcheck",  0);
	solver.set("inprocessing", 0);
	solver.set("report",       0);
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
	ExhaustiveSearch<FastPolicy> propagator(&solver, opts, proc);

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
	for (int i = 0; i < cube_amount; ++i) {
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
		cerr << "Usage: " << argv[0] << " <template_id> (# of free vars to remove) (maximum # of cubes)\n";
		return 1;
	}

	int template_id     = atoi(argv[1]) + 1; // match Python: template_id = int(sys.argv[2]) + 1
	int observed_syms_A = 10;
	if (argc > 2)
		CUBE_R_PARAM = atoi(argv[2]);
	if (argc > 3)
		CUBE_LIMIT = atoi(argv[3]);
	bool can_forget = true;

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
	cout << "can_forget             : " << can_forget << "\n";

	if (observed_syms_A > 10) {
		cerr << "Too many symbols observed; at most 10 per square.\n";
		return 1;
	}
	if (observed_syms_A <= 0) {
		cerr << "At least one symbol transversal must be observed in either square.\n";
		return 1;
	}

	setup(template_id);

	long long sol_count = runEncoding(template_path, template_id, observed_syms_A, can_forget, 10);

	cout << "\n=== FINAL RESULTS FOR TEMPLATE " << (template_id - 1) << " ===\n";
	cout << "Total partial solutions found: " << sol_count << "\n";
	cout << "Total refinements found: " << get_refinement_count() << "\n";
	cout << "Total early blocking attempts: " << early_blocks << "/" << early_blocks_total << "\n";
	cout << "Total cubes: " << cube_count << "\n";

	print_substep_timings_log(init_creation_time, 
		total_minimize_convert, total_minimize_cleanup, total_minimize_remove,
		total_cube_gen_time, total_cube_creation_time, total_cube_solve_time);

	return 0;
}

/*

TODO: figure out a way to print CPU times, all of these are WALL times (CaDiCaL::Terminator or expose solver->internal somehow? i think its private so id need to expose it again)

TODO: make get_refinements check the transversals in A and B:
	If (A == 0 and B == 0) then stop early and return 0
	If (A == 0 and B == order) or (B == order and A == 0) then only create half the constraints (can do this by setting the one with transverals as A and the other as B)
	else create the full constraints

TODO: *summary python script, takes in log Id and number of logs, the gets median, average and mode of the logs
	A log is simply a txt file of the results

TODO: run compute canada
	A) need to be able to get all templates individually on compute canada
	B) need to be able to refine templates into candidate lines individually on compute canada

TODO: optional but could restore main functionality in libexact_partial_solution_refinement.cpp so it can still independentally be used as a "SAT2" step like before
	This is not needed, only really applies if we want to independentally verify the correctness of the file and its implementation

*/