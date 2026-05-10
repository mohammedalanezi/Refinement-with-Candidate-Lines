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

using namespace std;

// ---------------------------------------------------------------
// Constants
// ---------------------------------------------------------------

#define ORDER_DEFINED
const int order        = 10;
const int latin_squares = 3;

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

long long runEncoding(const string& template_path, int template_id, 
					  int observed_syms_A, int observed_syms_B, 
					  bool can_forget) {
	CaDiCaL::Solver solver;
	solver.set("factor",       0);
	solver.set("factorcheck",  0);
	solver.set("inprocessing", 0);
	solver.set("report", 1);
	solver.set("quiet",        0);
	solver.set("verbose",      1);

	// ---- Load template ----
	cout << "Loading template from: " << template_path << "\n";
	auto tmpl = unloadTemplate(template_path);
	if (tmpl[0].empty() || tmpl[1].empty()) {
		cerr << "Failed to load a valid template.\n";
		return -1;
	}

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
	cout << "	Writing latin square constraints.\n";
	for (int sq = 0; sq < latin_squares; ++sq)
		encodeLatinSquare(solver, sq);

	// ---- Orthogonality constraints ----
	cout << "	Writing orthogonality constraints.\n";
	encodeMyrvoldOrthogonality(solver);

	// ---- Symmetry breaking (from template, row 0 only) ----
	cout << "	Writing symmetry breaking.\n";
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
	cout << "	Writing Gill encoding.\n";
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
	cout << "	Writing template restrictions.\n";
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

	// ---- Collect observed variables ----
	vector<int> observed;
	observed.reserve(
		(observed_syms_A + observed_syms_B) * order * order);

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
	opts.can_forget = can_forget;
	opts.solution_callback = solve_partial_solution;

	ExhaustiveSearch propagator(&solver, opts);

	auto solve_start = chrono::steady_clock::now();
	int  result      = solver.solve();
	double solve_elapsed = chrono::duration<double>(chrono::steady_clock::now() - solve_start).count();
	long long sol_count = propagator.get_solution_count();

	cout << "SAT result   : " << (result == 10 ? "SAT" : (result == 20 ? "UNSAT" : "UNKNOWN")) << "\n";
	cout << "Solutions    : " << sol_count << "\n";
	cout << "Solving Wall time : " << solve_elapsed << "s\n";

	return sol_count;
}

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

	string parent_dir    = "../";
	string template_path = parent_dir + "refinements and candidate lines/templates/" + to_string(template_id) + "-template.txt";

	cout << "=== Finding all partial solutions for template " << (template_id - 1) << " ===\n";
	cout << "observed_syms_A        : " << observed_syms_A        << "\n";
	cout << "observed_syms_B        : " << observed_syms_B        << "\n";

	if (observed_syms_A > 10 || observed_syms_B > 10) {
		cerr << "Too many symbols observed; at most 10 per square.\n";
		return 1;
	}
	if (observed_syms_A <= 0 && observed_syms_B <= 0) {
		cerr << "At least one symbol transversal must be observed in either square.\n";
		return 1;
	}

	setup(template_id);

	long long sol_count = runEncoding(template_path, template_id, observed_syms_A, observed_syms_B, /*can_forget=*/true);

	cout << "\n=== FINAL RESULTS FOR TEMPLATE " << (template_id - 1) << " ===\n";
	cout << "Total partial solutions found: " << sol_count << "\n";
	cout << "Total refinements found: " << get_refinement_count() << "\n";

	print_substep_timings_log();

	return 0;
}