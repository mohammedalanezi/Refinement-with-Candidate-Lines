/**
 * all_net_encoding.cpp
 *
 * C++ port of all_net_encoding.py by Mohammed Al-Anezi.
 *
 * Builds a SAT instance encoding three mutually orthogonal Latin squares
 * (Q, Z, P of order 10) with template-based symmetry breaking and Gill
 * parity constraints, then exhaustively enumerates all valid (A, B) pairs
 * by observing the symbol-transversal variables of Q and Z.
 *
 * Usage:
 *   ./all_net_encoding <template_id> <observed_syms_A (0-10)> <observed_syms_B (0-10)>
 */

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

#define MULTI_THREADING 0 // if I wanna add multi threading to substep then i need a worker and pool system
#define CUBE_CONQUER    1

// ---------------------------------------------------------------
// Cubing backend selector
//
//   USE_MARCH_CU 1  ->  shell out to march_cu (Curtis Bright's CnC fork)
//                       uses -r (free-vars-to-remove) and -m (max var index)
//                       to restrict branching to square Q only (vars 1-1000).
//                       Path is set via g_march_cu_path in main().
//
//   USE_MARCH_CU 0  ->  use CaDiCaL's built-in generate_cubes(depth)
//                       controlled by the depth parameter passed to runEncoding.
// ---------------------------------------------------------------
#define USE_MARCH_CU    1

// Number of free variables march_cu removes before emitting a cube (-r param).
// Increase this to get more cubes (each harder cube). Tune until each cube solves in seconds to low minutes.
#define CUBE_R_PARAM    20

using namespace std;

// ---------------------------------------------------------------
// Constants
// ---------------------------------------------------------------

#define ORDER_DEFINED
const int order        = 10;
const int latin_squares = 3;

// max variable index for square Q (sq=0): vars 1 ... order^3, sent to march_cu's -m flag so it only branches on Q's variables
const int Q_MAX_VAR = order * order * order;  // = 1000

double creation_time = 0.0f;

string g_march_cu_path; // Path to the march_cu binary; set in main() from march_cu_dir.

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
// Clause helpers
// ---------------------------------------------------------------

static inline void add_clause(CaDiCaL::Solver& solver, initializer_list<int> lits) {
	for (int l : lits) solver.add(l);
	solver.add(0);
}

static inline void add_clause(CaDiCaL::Solver& solver, const vector<int>& lits) {
	for (int l : lits) solver.add(l);
	solver.add(0);
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
//   (z ∧ p) -> q   ⟺   -z ∨ -p ∨  q
//   (z ∧ q) -> p   ⟺   -z ∨ -q ∨  p
//   (p ∧ q) -> z   ⟺   -p ∨ -q ∨  z
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
#if CUBE_CONQUER == 0 || USE_MARCH_CU == 1
struct FastSolutionProcessor {
	FastSolutionProcessor() {}
	void operator()(const std::vector<int>& solution) const {
		solve_partial_solution(solution);
	}
	explicit operator bool() const { return true; }
};
#elif CUBE_CONQUER == 1 && USE_MARCH_CU == 0
struct FastSolutionProcessor {
	long long &global_solution_count;          // shared counter
	std::unordered_set<uint64_t> *global_seen;

	// Constructor
	FastSolutionProcessor(long long &counter, std::unordered_set<uint64_t> *dedup = nullptr) : global_solution_count(counter), global_seen(dedup) {}

	// Called for every partial solution found inside a cube
	void operator()(const std::vector<int>& sol) const {
		// Cross-cube deduplication (only if a set is provided)
		if (global_seen) {
			uint64_t h = es_wyhash(sol.data(), sol.size() * sizeof(int), 0x517cc1b727220a95ULL);
			if (!global_seen->insert(h).second)
				return;   // duplicate – skip counting and refinement
		}
		++global_solution_count;
		solve_partial_solution(sol);
	}

	explicit operator bool() const { return true; }
};
#endif

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
// Cube generation — two backends selected by USE_MARCH_CU
// ---------------------------------------------------------------

#if CUBE_CONQUER == 1
	#if USE_MARCH_CU == 1
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
vector<vector<int>> generateCubes(
		const vector<vector<vector<int>>>& tmpl,
		const string& parent_dir, int template_id, int /*cube_depth_unused*/) {
	string cnf_path   = parent_dir + "tmp_t" + to_string(template_id) + ".cnf";
	string cubes_path = parent_dir + "tmp_t" + to_string(template_id) + "_cubes.icnf";

	// Step 1: build a temporary solver just to dump the DIMACS file
	cout << "  Writing CNF to: " << cnf_path << "\n";
	{
		CaDiCaL::Solver dumper;
		dumper.set("inprocessing", 0);
		dumper.set("factor",       0);
		buildFormula(dumper, tmpl);
		dumper.write_dimacs(cnf_path.c_str());
	}

	// Step 2: shell out to march_cu
	//   -r CUBE_R_PARAM : stop after removing this many free variables
	//   -m Q_MAX_VAR    : only branch on vars <= 1000 (square Q)
	//   -o cubes_path   : write cubes here
	ostringstream cmd;
	cmd << g_march_cu_path << " " << cnf_path << " -r " << CUBE_R_PARAM << " -m " << Q_MAX_VAR << " -o " << cubes_path;

	cout << "  Running: " << cmd.str() << "\n";
	auto t0 = chrono::steady_clock::now();

	int ret = system(cmd.str().c_str());
	double elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();

	if (ret != 0) {
		cerr << "march_cu failed with exit code " << ret << "\n";
		return {};
	}
	cout << "  Cubing time: " << elapsed << "s\n";

	// Step 3: parse the .icnf output
	auto cubes = parseCubesFile(cubes_path);
	cout << "  Cubes generated: " << cubes.size() << "\n";
	return cubes;
}
	#else // USE_MARCH_CU == 0, use CaDiCaL's built-in lookahead cuber
// Generates cubes using CaDiCaL's generate_cubes(depth).
// NOTE: depth-based splitting can produce unbalanced cubes. Prefer the march_cu backend (-r param) for production runs.
vector<vector<int>> generateCubes(
		const vector<vector<vector<int>>>& tmpl,
		const string& /*parent_dir_unused*/,
		int /*template_id_unused*/,
		int cube_depth)
{
	cout << "  Cubing phase (CaDiCaL, depth=" << cube_depth << ")...\n";
	auto t0 = chrono::steady_clock::now();

	CaDiCaL::Solver cuber;
	cuber.set("inprocessing", 0);
	cuber.set("factor",       0);
	cuber.set("quiet",        1);
	buildFormula(cuber, tmpl);

	auto result = cuber.generate_cubes(cube_depth, /*min_depth=*/0);

	double elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	cout << "  Cubes generated: " << result.cubes.size() << "\n";
	cout << "  Cubing time    : " << elapsed << "s\n";

	return result.cubes;
}
	#endif // USE_MARCH_CU
#endif // CUBE_CONQUER

// ---------------------------------------------------------------
// Solves a single cube: rebuilds the formula, adds cube lits as
// hard unit clauses, then runs the exhaustive enumeration.
// ---------------------------------------------------------------
long long solveOneCube(const vector<vector<vector<int>>>& tmpl,
					   const vector<int>&                 cube,
					   int observed_syms_A, int observed_syms_B,
					   bool can_forget, int cube_index,
					   FastSolutionProcessor& proc) {
	CaDiCaL::Solver solver;
	solver.set("factor",       0);
	solver.set("factorcheck",  0);
	solver.set("inprocessing", 0);
	solver.set("report",       0);

	buildFormula(solver, tmpl);

	// Fix the cube as hard unit clauses (not assumptions — you want
	// the exhaustive propagator to see them as permanent facts)
	for (int lit : cube)
		solver.clause({lit});

	// Observed variables (same as before)
	vector<int> observed;
	observed.reserve((observed_syms_A + observed_syms_B) * order * order);
	for (int s = 0; s < observed_syms_A; ++s)
		for (int r = 0; r < order; ++r)
			for (int c = 0; c < order; ++c)
				observed.push_back(var(0, r, c, s));
	for (int s = 0; s < observed_syms_B; ++s)
		for (int r = 0; r < order; ++r)
			for (int c = 0; c < order; ++c)
				observed.push_back(var(1, r, c, s));

	ExhaustiveSearchOptions opts;
	opts.to_observe = observed;
	opts.only_neg   = true;
	opts.can_forget = can_forget;

	ExhaustiveSearch<FastSolutionProcessor> propagator(&solver, opts, proc);

	auto t0 = chrono::steady_clock::now();
	int result = solver.solve();
	double elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();

	long long count = propagator.get_solution_count();
	cout << "  Cube " << cube_index << ": "
		 //<< (result == 10 ? "SAT | " : "UNSAT | ")
		 << count << " partial solutions, took " << elapsed << "s\n";

	return count;
}

#if CUBE_CONQUER == 0
long long runEncoding(const string& template_path, int template_id, 
					  int observed_syms_A, int observed_syms_B, 
					  bool can_forget) {
	auto timer = chrono::steady_clock::now();
	CaDiCaL::Solver solver;
	solver.set("factor",       0);
	solver.set("factorcheck",  0);
	solver.set("inprocessing", 0);
	//solver.set("report", 1);
	//solver.set("quiet",        0);
	//solver.set("verbose",      1);

	// ---- Load template ----
	cout << "Loading template from: " << template_path << "\n";
	auto tmpl = unloadTemplate(template_path);
	if (tmpl[0].empty() || tmpl[1].empty()) {
		cerr << "Failed to load a valid template.\n";
		return -1;
	}

	int next_aux = buildFormula(solver, tmpl);

	// ---- Collect observed variables ----
	vector<int> observed;
	observed.reserve((observed_syms_A + observed_syms_B) * order * order);

	for (int s = 0; s < observed_syms_A; ++s)
		for (int r = 0; r < order; ++r)
			for (int c = 0; c < order; ++c)
				observed.push_back(var(0, r, c, s));

	for (int s = 0; s < observed_syms_B; ++s)
		for (int r = 0; r < order; ++r)
			for (int c = 0; c < order; ++c)
				observed.push_back(var(1, r, c, s));

	cout << "Observed variables : " << observed.size() << "\n";
	cout << "Total variables    : " << (next_aux - 1) << "\n";

	// ---- Run exhaustive SAT solver ----
	cout << "Running exhaustive SAT solver (can_forget=" << can_forget << ")...\n";

	ExhaustiveSearchOptions opts;
	opts.to_observe = observed;
	opts.only_neg = true;
	opts.can_forget = can_forget;

	ExhaustiveSearch<FastSolutionProcessor> propagator(&solver, opts);

	creation_time = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	auto solve_start = chrono::steady_clock::now();
	int  result      = solver.solve();
	double solve_elapsed = chrono::duration<double>(chrono::steady_clock::now() - solve_start).count();
	long long sol_count = propagator.get_solution_count();

	cout << "SAT result   			: " << (result == 10 ? "SAT" : (result == 20 ? "UNSAT" : "UNKNOWN")) << "\n";
	cout << "Solutions    			: " << sol_count << "\n";
	cout << "SAT Creation Wall time	: " << creation_time << "s\n";
	cout << "Solving Wall time 		: " << solve_elapsed << "s\n";

	return sol_count;
}
#else
long long runEncoding(const string& template_path, int template_id,
					  int observed_syms_A, int observed_syms_B,
					  bool can_forget, int cube_depth = 8) {
	auto timer = chrono::steady_clock::now();
	cout << "Loading template from: " << template_path << "\n";
	auto tmpl = unloadTemplate(template_path);
	if (tmpl[0].empty() || tmpl[1].empty()) {
		cerr << "Failed to load a valid template.\n";
		return -1;
	}

	cout << "Cubing backend     : "
#if USE_MARCH_CU
		 << "march_cu (path=" << g_march_cu_path << ", -r=" << CUBE_R_PARAM << ", -m=" << Q_MAX_VAR << " [Q vars only])\n";
#else
		 << "CaDiCaL generate_cubes (depth=" << cube_depth << ")\n";
#endif

	// --- Cubing phase ---
	string parent_dir = "./";

	vector<vector<int>> cubes = generateCubes(tmpl, parent_dir, template_id, cube_depth);
	if (cubes.empty()) {
		cout << "No cubes generated (formula UNSAT during cubing or march_cu error).\n";
		return 0;
	}

	// --- Shared state for all cubes ---
	std::unordered_set<uint64_t> global_seen;
#if CUBE_CONQUER == 0 || USE_MARCH_CU == 1
	FastSolutionProcessor proc = FastSolutionProcessor();
#else
	long long total_solutions = 0;
	FastSolutionProcessor proc(total_solutions, &global_seen);
#endif

	creation_time = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	
	// --- Conquer phase (sequential for now; trivial to parallelise later) ---
	long long total = 0;
	auto wall_start = chrono::steady_clock::now();

	for (int i = 0; i < (int)cubes.size(); ++i)
		total += solveOneCube(tmpl, cubes[i], observed_syms_A, observed_syms_B, can_forget, i, proc);

	double total_elapsed = chrono::duration<double>(chrono::steady_clock::now() - wall_start).count();

	cout << "\nConquer wall time                : " << total_elapsed << "s\n";
	cout << "Solutions (total)                : " << total << "\n";
#if CUBE_CONQUER == 1 && USE_MARCH_CU == 0
	cout << "Solutions (total duplicate free) : " << total_solutions << "\n";
#endif

	return total;
}
#endif

// ---------------------------------------------------------------
// Main
// ---------------------------------------------------------------

int main(int argc, char* argv[]) {
	if (argc < 4) {
		cerr << "Usage: " << argv[0] << " <template_id> <observed_syms_A (0-10)> <observed_syms_B (0-10)>\n";
		return 1;
	}

	int template_id     = atoi(argv[1]) + 1; // match Python: template_id = int(sys.argv[2]) + 1
	int observed_syms_A = atoi(argv[2]);
	int observed_syms_B = atoi(argv[3]);
	bool can_forget = true;

	string parent_dir    = "../";
	string template_path = parent_dir + "refinements and candidate lines/templates/" + to_string(template_id) + "-template.txt";

	// TODO: On the cluster, use the full absolute path, e.g.: g_march_cu_path = string(getenv("HOME")) + "/CnC-master/march_cu";
	string march_cu_dir  = "../CnC-master/march_cu";
	g_march_cu_path      = march_cu_dir + "/march_cu";

	cout << "=== Finding all partial solutions for template " << (template_id - 1) << " ===\n";
	cout << "observed_syms_A        : " << observed_syms_A        << "\n";
	cout << "observed_syms_B        : " << observed_syms_B        << "\n";
	cout << "can_forget             : " << can_forget << "\n";

	if (observed_syms_A > 10 || observed_syms_B > 10) {
		cerr << "Too many symbols observed; at most 10 per square.\n";
		return 1;
	}
	if (observed_syms_A <= 0 && observed_syms_B <= 0) {
		cerr << "At least one symbol transversal must be observed in either square.\n";
		return 1;
	}

	setup(template_id);

	long long sol_count = runEncoding(template_path, template_id, observed_syms_A, observed_syms_B, can_forget, 10);

	cout << "\n=== FINAL RESULTS FOR TEMPLATE " << (template_id - 1) << " ===\n";
	cout << "Total partial solutions found: " << sol_count << "\n";
	cout << "Total refinements found: " << get_refinement_count() << "\n";

	print_substep_timings_log(creation_time);

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

@mogaming 
fri:
	*recode summary script with built in RANDOMIZED SEED, i think the default seed is always 0
	run compute canada
	1a. need to be able to get all templates individually on compute canada
	1b. need to be able to refine templates into candidate lines individually on compute canada
	meeting

*/