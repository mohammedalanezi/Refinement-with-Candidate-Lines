#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <chrono>
#include <cstdlib>
#include <algorithm>
#include <cstdint>
#include <csignal>
#include <cstdio>

#include "cadical.hpp"
#include "exhaustive.hpp"

#define FULL_DUMP 0 // if we dump irredundant clauses/unit clauses to march_cu
#define MAX_CUBES 0 // maximum cubes we process, infinite when <=0, this is for early termination
#define TRACK_TIME 1 // Track timings, GLOBAL WALL TIME ALWAYS TRACKED

#define WRITE_REFINEMENTS 1 // If we write out the binary refinement file or not

#define CANEARLY 1 // 1 is fastest
#define MINIMIZE 0 // 0 is fastest
#define CANFORGET 1 // 1 is fastest

#define MIN_LINES 5 // 3-5 faster than 6 with no minimzation 

#define ISCLUSTER 1

using namespace std; 

// ---------------------------------------------------------------
// Constants/Variables
// ---------------------------------------------------------------

bool g_test_mode = false;
bool g_timeout_check_active = false;
double g_cube_timeout_seconds = 0.0;
int cubes_to_test = 3;
chrono::steady_clock::time_point g_cube_start_time;

struct CubeTimeoutException {};

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

double total_tune_time = 0.0f;

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

int TEMPLATE_ID = 0; // Current template we are solving
int SOl_COUNT = 0; // Total number of partial solutions
int SAT_SEED = 0; // Seed of the Cubes, <= -1 adds no seed
string JOB_ID = ""; // Job_id used for repeated calls to the same template

#include "partial_solution_refinement.cpp"

void print_output(bool completed);
vector<vector<int>> generateCubes(const vector<vector<vector<int>>>& tmpl, const string& parent_dir);

static void handle_sigterm(int) {
	print_output(false);
	std::fflush(stdout);   // flush C-style stdout (printf, etc.)
	std::fflush(stderr);
	std::cout.flush();     // flush C++ streams too
	std::cerr.flush();
	flush_output();
	std::_Exit(0);         // hard exit -- skips destructors which could hang
}

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
// Template loading from binary file
// ---------------------------------------------------------------

std::vector<std::vector<std::vector<int>>> read_template_from_binary(const std::string& binary_path) {
	// Result: 2 squares, each 10 rows of 10 ints
	std::vector<std::vector<std::vector<int>>> tmpl(2, std::vector<std::vector<int>>(10, std::vector<int>(10, 0)));

	std::ifstream in(binary_path, std::ios::binary);
	if (!in) {
		std::cerr << "Cannot open binary file: " << binary_path << "\n";
		return tmpl;   // empty template
	}

	// Each template occupies exactly 25 bytes
	constexpr std::streamoff block_size = 25;
	in.seekg(TEMPLATE_ID * block_size);
	if (!in) {
		std::cerr << "Invalid template ID or seek error\n";
		return tmpl;
	}

	unsigned char buffer[block_size];
	in.read(reinterpret_cast<char*>(buffer), block_size);
	if (in.gcount() != block_size) {
		std::cerr << "Could not read full template block\n";
		return tmpl;
	}

	// Unpack bits in the same order they were written:
	// square 0 rows 0..9 cols 0..9, then square 1 rows 0..9 cols 0..9
	int bit_index = 0;
	for (int sq = 0; sq < 2; ++sq)
		for (int row = 0; row < 10; ++row)
			for (int col = 0; col < 10; ++col) {
				int byte_idx = bit_index / 8;
				int bit_pos  = bit_index % 8;
				int val = (buffer[byte_idx] >> bit_pos) & 1;
				tmpl[sq][row][col] = val;
				++bit_index;
			}

	return tmpl;
}

// ---------------------------------------------------------------
// Latin-square encoding
//
// For every (x, y) pair three families of at-least-one clauses are added together with all pairwise at-most-one (binary exclusion) clauses:
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
// Myrvold orthogonality encoding
//
// Uses the auxiliary square P (sq=2) to couple Q (sq=0) and Z (sq=1).
// For every i, i', j, k:
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
		if (g_timeout_check_active) { // only active while r-tuning is probing a sample cube
			double elapsed = chrono::duration<double>(chrono::steady_clock::now() - g_cube_start_time).count();
			if (elapsed > g_cube_timeout_seconds) {
				cout << "timed out\n";
				throw CubeTimeoutException{};
			}
		}

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

// ---------------------------------------------------------------
// Adaptive r-parameter tuning
// ---------------------------------------------------------------
static const double R_TEST_TIMEOUT_SECONDS = 60.0 * 3.0;
static const double R_TEST_TARGET_SECONDS = 75.0;
static const double R_INCREASE_FACTOR = 1.20; // factor r is grown by each failure 

void print_r_parameter() {
	cout << "r_parameter            : " << CUBE_R_PARAM << "\n";
	cout.flush();
}

bool testSolveCube(const vector<int>& cube, double& elapsed_out) {
	CaDiCaL::Solver copy;
	solver.copy(copy);
	for (int lit : cube)
		copy.clause(lit);

	ExhaustiveSearch<FastPolicy> propagator_(&copy, opts, FastPolicy());

	g_test_mode = true;
	g_timeout_check_active = true;
	g_cube_timeout_seconds = R_TEST_TIMEOUT_SECONDS;
	g_cube_start_time = chrono::steady_clock::now();

	bool timed_out = false;
	try {
		copy.solve();
	} catch (const CubeTimeoutException&) {
		timed_out = true;
	}

	g_timeout_check_active = false;
	g_test_mode = false;

	elapsed_out = chrono::duration<double>(chrono::steady_clock::now() - g_cube_start_time).count();
	return timed_out;
}

vector<int> pickSampleCubeIndices(int cube_amount) {
	vector<int> idxs;
	if (cube_amount <= 0) return idxs;

	if (cube_amount <= cubes_to_test) {
		for (int i = 0; i < cube_amount; ++i)
			idxs.push_back(i);
		return idxs;
	}

	for (int i = 0; i < cubes_to_test; ++i) {
		int start = (i * cube_amount) / cubes_to_test;
		int end   = ((i + 1) * cube_amount) / cubes_to_test;

		// pick uniformly from [start, end)
		int idx = start + rand() % max(1, end - start);
		idxs.push_back(idx);
	}
	return idxs;
}

vector<vector<int>> tuneRParameter(const vector<vector<vector<int>>>& tmpl, const string& parent_dir) {
#if TRACK_TIME
	auto t0 = chrono::steady_clock::now();
#endif
	vector<vector<int>> cubes;

	int prev_r = -1; // best so far
	double prev_estimate = -1.0;
	vector<vector<int>> prev_cubes;

	cout << "[r-tuning] START:\n";

	while (true) {
		cout << "\n[r-tuning] Generating cubes with r=" << CUBE_R_PARAM << " to test timing...\n";
		cubes = generateCubes(tmpl, parent_dir);
		if (cubes.empty()) {
			cout << "[r-tuning] No cubes generated; aborting r-tuning.\n";
			break;
		}

		vector<int> sample = pickSampleCubeIndices((int)cubes.size());

		bool any_timeout = false;
		double total_time = 0.0;
		int tested = 0;

		for (int idx : sample) {
			double elapsed = 0.0;
			bool timed_out = testSolveCube(cubes[idx], elapsed);
			cout << "[r-tuning] Test cube " << idx << "/" << cubes.size() << ": " << (timed_out ? "TIMEOUT" : "solved") << " in " << elapsed << "s\n";
			cout.flush();

			if (timed_out) {
				any_timeout = true;
				break;
			}
			total_time += elapsed;
			++tested;
		}

		if (any_timeout) {
			CUBE_R_PARAM = max(CUBE_R_PARAM + 1, (int)std::round(CUBE_R_PARAM * R_INCREASE_FACTOR));
			print_r_parameter();
			continue;
		}

		double avg = tested > 0 ? total_time / tested : 0.0;
		double estimate = cubes.size() * avg; // total cubes * (tested_cube_time / tested_cube_amount)
		cout << "[r-tuning] Average test cube time: " << avg << "s over " << tested << " cube(s)\n";
		cout << "[r-tuning] Estimated total solve time at r=" << CUBE_R_PARAM << ": " << estimate << "s (" << cubes.size() << " cubes * " << avg << "s avg)\n";

		if (avg <= R_TEST_TARGET_SECONDS) {
			cout << "r-tuning] Average test cube time below target: " << R_TEST_TARGET_SECONDS << "s, ending early\n";
			CUBE_R_PARAM = -CUBE_R_PARAM; 
			print_r_parameter();
			break;
		}

		if (prev_estimate >= 0.0 && estimate > prev_estimate) {
			cout << "[r-tuning] Estimated time increased (" << estimate << "s > " << prev_estimate << "s at r=" << prev_r << "); reverting to r=" << prev_r << " and continuing.\n";
			CUBE_R_PARAM = -prev_r;
			cubes = std::move(prev_cubes);
			print_r_parameter();
			break;
		}

		prev_r = CUBE_R_PARAM;
		prev_estimate = estimate;
		prev_cubes = cubes;

		CUBE_R_PARAM = max(CUBE_R_PARAM + 1, (int)std::round(CUBE_R_PARAM * R_INCREASE_FACTOR));
		print_r_parameter();
	}

	cout << "[r-tuning] DONE, resetting variables:\n";
	//total_refinement_solve_time = 0.0;
	//total_refinement_early_blocking = 0.0;
	//total_line_covering_time = 0.0;
	//total_line_intersection_time = 0.0;

	partial_count = 0;
	total_refinements = 0;
	skipped_partial_solutions = 0;
	
#if TRACK_TIME
	total_tune_time = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
#endif

	return cubes;
}

// Generates cubes by:
//   1. Writing the formula to a temporary DIMACS .cnf file
//   2. Shelling out to march_cu with:
//        -r CUBE_R_PARAM   (stop once this many free vars have been removed)
//        -m Q_MAX_VAR      (only branch on square Q's variables, i.e. vars 1-1000, so every cube fixes a distinct partial assignment of Q
//                           and refinement sees no duplicate work across cubes)
//   3. Parsing the resulting .icnf file
vector<vector<int>> generateCubes(const vector<vector<vector<int>>>& tmpl, const string& parent_dir) {
#if TRACK_TIME
	auto t0 = chrono::steady_clock::now();
#endif
	string cnf_path   = parent_dir + "/tmp" + to_string(TEMPLATE_ID) + ".cnf";
	string cubes_path = parent_dir + "/tmp" + to_string(TEMPLATE_ID) + "_cubes.icnf";

	if (CUBE_R_PARAM > 0) { // negative r values imply we have already created the cubes
		{ // Step 1: build a temporary solver just to dump the DIMACS file
			cout << "  Writing CNF to: " << cnf_path << "\n";
			CaDiCaL::Solver dumper; 
			solver.copy(dumper);
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
		cmd << g_march_cu_path << " " << cnf_path << " -r " << abs(CUBE_R_PARAM) << " -m " << Q_MAX_VAR;
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
	}

	auto cubes = parseCubesFile(cubes_path); // Step 3: parse the .icnf output
	cout << "  Cubes generated: " << cubes.size() << "\n";
	cube_count = cubes.size();
	return cubes;
}

// ---------------------------------------------------------------
// Solves a single cube: reuses central solver, adds cube as assumption literals, then runs the exhaustive enumeration.
// ---------------------------------------------------------------
long long solveOneCube(const vector<vector<vector<int>>>& tmpl, const vector<int>& cube, const int& cube_index) {
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
	cout << "	Early clauses: " << propagator_.get_early_blocking_count() << "/" << propagator_.get_attempt_early_blocking_count() << "(" << total_refinements << ", " << skipped_partial_solutions << ")" << endl;

	early_blocks += propagator_.get_early_blocking_count();
	early_blocks_total += propagator_.get_attempt_early_blocking_count();

	return count;
}

// ---------------------------------------------------------------
// Runs the entire encoding process from creating the solver to generating to cubes, then finishing by solving them all.
// ---------------------------------------------------------------
void runEncoding(int observed_syms_A, bool can_forget) {
	auto timer = chrono::steady_clock::now();
	cout << "Running Encoding:\n";

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

	int display_r = CUBE_R_PARAM < 0 ? -CUBE_R_PARAM : CUBE_R_PARAM;
	cout << "	Generating Cubes: march_cu (path=" << g_march_cu_path << ", -r=" << display_r << ", -m=" << Q_MAX_VAR << " [Q vars only]";
	if (CUBE_LIMIT > 0)
		cout << ", -l=" << CUBE_LIMIT;
	cout << ")\n";

	// --- Cubing phase ---
	vector<vector<int>> cubes = (CUBE_R_PARAM > 0) ? tuneRParameter(tmpl, output_path) : generateCubes(tmpl, output_path);
	if (cubes.empty()) {
		cout << "No cubes generated (formula UNSAT during cubing or march_cu error).\n";
		return;
	}

	init_creation_time = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	
	// --- Conquer phase (sequential for now; trivial to parallelise later) ---
	int interval = max(1, min(2000, (int)cubes.size()/10));
	auto wall_start = chrono::steady_clock::now();

	int cube_amount = cubes.size();
#if MAX_CUBES > 0
	if(cubes.size() > MAX_CUBES)
		cube_amount = MAX_CUBES;
#endif

	cout << "	Solving Cubes:" << endl;
	for (int i = CUBE_START; i < cube_amount; ++i) {
		SOl_COUNT += solveOneCube(tmpl, cubes[i], i);
		if(i % interval == 0) {
			cout << i+1 << "/" << cubes.size() << ": average solve: " << total_cube_solve_time/(i + 1) << "s, average create: " << total_cube_creation_time/(i + 1) << "s, ETA: " << cubes.size() * (total_cube_solve_time/(i + 1) + total_cube_creation_time/(i + 1)) << "s" << endl;
			cout.flush(); // to ensure cluster updates encase of timeout
			flush_output(); // ensure the refinements keep up
		}
	}

	double total_elapsed = chrono::duration<double>(chrono::steady_clock::now() - wall_start).count();

	cout << "\nTotal wall time: " << total_elapsed << "s\n";
	cout << "Partial Solutions: " << SOl_COUNT << "\n";
}

void print_output(bool completed) {
	if(completed) 
		cout << "\n=== FINAL RESULTS FOR TEMPLATE " << TEMPLATE_ID << " ===\n";
	else
		cout << "\n=== INCOMPLETE RESULTS FOR TEMPLATE " << TEMPLATE_ID << " ===\n";
	cout << "Total partial solutions found: " << SOl_COUNT << "\n";
	cout << "Total refinements found: " << total_refinements << "\n";
	cout << "Total early blocking attempts: " << early_blocks << "/" << early_blocks_total << "\n";
	cout << "Total cubes: " << cube_count << "\n";

	print_substep_timings_log(init_creation_time, total_tune_time,
		total_minimize_setup, total_minimize_remove,
		total_cube_gen_time, total_cube_creation_time, total_cube_solve_time);
}

// ---------------------------------------------------------------
// Main
// ---------------------------------------------------------------
int main(int argc, char* argv[]) {
	std::signal(SIGTERM, handle_sigterm);
	std::signal(SIGINT,  handle_sigterm);

	if (argc < 3) {
		cerr << "Usage: " << argv[0] << " <output_directory> <TEMPLATE_ID> (# of free vars to remove) (starting cube) (jobid) (seed) (maximum # of cubes)\n";
		return 1;
	}

	string output_path 	= argv[1];
	TEMPLATE_ID     = atoi(argv[2]); 
	int observed_syms_A = 10;
	if (argc > 3) CUBE_R_PARAM 	= atoi(argv[3]);
	if (argc > 4) CUBE_START 	= atoi(argv[4]);
	if (argc > 5) JOB_ID		= argv[5];
	if (argc > 6) SAT_SEED 		= atoi(argv[6]);
	if (argc > 7) CUBE_LIMIT 	= atoi(argv[7]);
	
	freopen((output_path + "/refinements_" + JOB_ID + ".log").c_str(), "w", stdout);
	freopen((output_path + "/refinements_" + JOB_ID + ".log").c_str(), "a", stderr); // Redirect all cout output into a log file instead of the terminal

#if ISCLUSTER == 1
	string project_dir	= string(getenv("HOME")) + "/projects/def-stevens/mo13";
	g_march_cu_path		= project_dir + "/CnC/march_cu/march_cu";
	std::string binary_file = project_dir + "/Refinement-with-Candidate-Lines/templates.bin";
#else
	string project_dir = ".";
	g_march_cu_path		= project_dir + "./CnC-master/march_cu/march_cu";
	std::string binary_file = project_dir + "/templates.bin";
#endif

	cout << "== Copy Model, each cube are turned into literals into their own solver copied from a base solver, no learned clauses transfer over. ==\n";
	cout << "=== Finding all partial solutions for template " << TEMPLATE_ID << " ===\n";
	cout << "observed_syms_A        : " << observed_syms_A        << "\n";
	print_r_parameter();
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
	
	cout << "	Loading template from: " << binary_file << "\n";
	tmpl = read_template_from_binary(binary_file);
	if (tmpl[0].empty() || tmpl[1].empty()) {
		cerr << "Failed to load a valid template.\n";
		return -1;
	}

	setup(tmpl, output_path, JOB_ID);
	runEncoding(observed_syms_A, CANFORGET);
	print_output(true);

	return 0;
}
