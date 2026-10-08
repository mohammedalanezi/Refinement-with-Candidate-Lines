/* template_dynamic.cpp
 *
 * Enumerates pairs (A,B) of orthogonal Latin squares of order 10 that refine one fixed template T, up to the automorphism group Aut(T).
 * T is a pair of 10x10 binary frequency squares (relation type 4^4), read from a text file or from a record of templates.bin.
 *
 * Refinement: symbols 0..3 are "relational", symbols 4..9 "non-relational". A square refines T when the class of the symbol in every cell matches the
 * template bit of that cell. A refining square is ten disjoint candidate lines, one per symbol.
 *
 * Pipeline
 *   1. Read T and compute Aut(T) with nauty (automorphisms.cpp).
 *   2. Build the CNF: Latin squares A and B, orthogonality (via auxiliary LS Z), the template constraints, and the static lex-leader clauses of Aut(T).
 *   3. CaDiCaL enumerates A only so DynamicAOnlyPolicy prunes partial A's and hands each complete A to the refinement step (partial_solution_refinement.cpp), which enumerates every compatible B.
 *   4. Each (A,B) pair goes through pairLevelAccept() before it is written.
 *
 * Symmetry breaking
 *   An element g of Aut(T) maps refining pairs to refining pairs. To keep one pair per orbit, (A,B) must be <= its image under g in canonical order, A compared before B. 
 *   The image is renormalized by the symbol relabeling sigma_g that restores the pinned row-0 labels:
 *
 *       sigma_g( A[ srcRow0[c] ] ) = row0LabelA[c]     for c = 0..9
 *
 *   Only then do the two sides lie in the same slice of the search space. Three places apply this:
 *   - CNF: elements whose sigma_g is constant, i.e. that fix row 0 setwise without transposing. These include square-swapping elements, since the CNF contains B.
 *   - DynamicAOnlyPolicy: the remaining elements that do not swap squares. sigma_g depends on A and is available once the source line of A is
 *     assigned; before that the element is skipped. B is not observed, so only A is compared.
 *   - pairLevelAccept(): every non-identity element, on the finished (A,B) pairs. This covers what the layers above cannot: elements that swap
 *     the squares, and elements that fix A but move B.
 * =============================================================================
 */
#include <array>
#include <fstream>
#include <vector>
#include <utility>
#include <string>
#include <iostream>
#include <cstdint>
#include <cassert>
#include <cstdlib>
#include <chrono>
#include <algorithm>
#include <atomic>
#include <thread>
#include <iomanip>
#include <memory>
#include <cstring>
#include <sstream>
#include <filesystem>

#include "cadical.hpp"
#include "proofsizetracer.hpp"
#include "exhaustive.hpp"
#include "4net_nauty.cpp"

// automorphisms.cpp computes Aut(T) for the concrete binary template.
namespace TemplateAutoNS {
#define main template_automorphisms_disabled_main
#include "automorphisms.cpp"
#undef main
}

using namespace std;

// ---- Build configuration ----
#define ISCLUSTER 1
// Refinement step (see partial_solution_refinement.cpp): 0 = custom exact cover, 1 = exact cover as a SAT instance.
#define SATREFINEMENT 1
#define WRITE_PROOFS 2            // 0 = none, 1 = one DRAT proof per cube solve, 2 = internal LRAT checking (checkproof) + DRAT proof size (ProofSizeTracer) per cube
#define WRITE_DYNAMIC_CLAUSES 1   // log automorphism-justified blocks to dynamic_clauses_<ID>.bin

constexpr int order = 10;

static int TEMPLATE_ID = -1; // Record of the template in templates.bin, or -1 if it was read from a text file

#if ISCLUSTER == 1
static const string project_dir = string(getenv("HOME") ? getenv("HOME") : ".") + "/projects/def-stevens/mo13";
static const string default_binary_file = project_dir + "/Refinement-with-Candidate-Lines/templates.bin";
static const string default_march_cu_path = project_dir + "/CnC/march_cu/march_cu";
static const string scratch_dir = string(getenv("SCRATCH") ? getenv("SCRATCH") : project_dir);
#else
static const string project_dir = ".";
static const string default_binary_file = project_dir + "/templates.bin";
static const string default_march_cu_path = project_dir + "/../CnC-master/march_cu/march_cu";
static const string scratch_dir = project_dir;
#endif

#define ORDER_DEFINED
#include "partial_solution_refinement.cpp"
#undef ORDER_DEFINED

// ---------------------------------------------------------------------------
// Cell and variable indexing
// ---------------------------------------------------------------------------
static constexpr int NCELLS = order * order;
array<pair<int8_t, int8_t>, NCELLS> canonicalCells{};  // canonical index -> (row, col)
static array<uint8_t, NCELLS> g_canonPoint{};          // canonical index -> flat cell
static array<uint8_t, NCELLS> g_pointCanon{};          // flat cell -> canonical index (inverse of g_canonPoint)

// A variable (1..order^3) -> flat cell and symbol
static array<uint8_t, order * order * order + 1> g_varPoint{};
static array<int8_t,  order * order * order + 1> g_varSym{};

// Canonical order: first column, then the rest of row 0, then the interior row by row
static void buildCanonicalOrder() {
	int idx = 0;
	for (int r = 0; r < order; ++r) canonicalCells[idx++] = {(int8_t)r, (int8_t)0};
	for (int c = 1; c < order; ++c) canonicalCells[idx++] = {(int8_t)0, (int8_t)c};
	for (int r = 1; r < order; ++r)
		for (int c = 1; c < order; ++c)
			canonicalCells[idx++] = {(int8_t)r, (int8_t)c};
	if (idx != NCELLS) {
		cerr << "Internal error: buildCanonicalOrder filled " << idx << " cells, expected " << NCELLS << "\n";
		exit(1);
	}

	for (int i = 0; i < NCELLS; ++i) {
		auto [r, c] = canonicalCells[i];
		g_canonPoint[i] = (uint8_t)(r * order + c);
		g_pointCanon[r * order + c] = (uint8_t)i;
	}

	for (int v = 1; v <= order * order * order; ++v) {
		const int a = v - 1;
		g_varSym[v]   = (int8_t)(a % order);
		g_varPoint[v] = (uint8_t)(a / order);   // r*order + c
	}
}

// One-hot SAT variable "square sq holds symbol s at (r,c)". sq: 0 = A, 1 = B, 2 = auxiliary square Z.
inline int var(int sq, int r, int c, int s) {
	return sq * order * order * order + r * order * order + c * order + s + 1;
}

// Class of a symbol: 0 for the relational symbols 0..3, 1 for the non-relational 4..9.
static inline int symClass(int s) { return s < 4 ? 0 : 1; }

// ---------------------------------------------------------------------------
// Template
// ---------------------------------------------------------------------------
// TEMPLATE_F[sq][r][c] = 1 iff the symbol of square sq at (r,c) is relational.
static int TEMPLATE_F[2][order][order]{};

// Checks the type 4^4 structure of whatever is in TEMPLATE_F, whichever reader filled it.
static bool validateTemplate() {
	for (int sq = 0; sq < 2; ++sq) {
		for (int r = 0; r < order; ++r) {
			int ones = 0;
			for (int c = 0; c < order; ++c) ones += TEMPLATE_F[sq][r][c];
			if (ones != 4) {
				cerr << "F" << sq << " row " << r << " has " << ones
					 << " ones; expected 4.\n";
				return false;
			}
		}
		for (int c = 0; c < order; ++c) {
			int ones = 0;
			for (int r = 0; r < order; ++r) ones += TEMPLATE_F[sq][r][c];
			if (ones != 4) {
				cerr << "F" << sq << " column " << c << " has " << ones
					 << " ones; expected 4.\n";
				return false;
			}
		}
	}

	// F0 xor F1 must equal (row < 4) xor (column < 4) at every cell.
	for (int r = 0; r < order; ++r)
		for (int c = 0; c < order; ++c) {
			int template_parity = TEMPLATE_F[0][r][c] ^ TEMPLATE_F[1][r][c];
			int row_col_parity = (r < 4 ? 1 : 0) ^ (c < 4 ? 1 : 0);
			if (template_parity != row_col_parity) {
				cerr << "Template parity check failed at (" << r << "," << c << ").\n";
				return false;
			}
		}
	return true;
}

// Reads record `template_id` of the packed template file: 25 bytes = 200 bits, square 0 then square 1, rows top to bottom, LSB of each byte first.
static bool readTemplateBinary(const string& binary_path, int template_id) {
	if (template_id < 0) {
		cerr << "Invalid template ID: " << template_id << "\n";
		return false;
	}

	ifstream in(binary_path, ios::binary);
	if (!in) {
		cerr << "Cannot open binary template file: " << binary_path << "\n";
		return false;
	}

	constexpr streamoff block_size = 25;
	in.seekg((streamoff)template_id * block_size);
	if (!in) {
		cerr << "Invalid template ID or seek error (id=" << template_id << ").\n";
		return false;
	}

	unsigned char buffer[block_size];
	in.read(reinterpret_cast<char*>(buffer), block_size);
	if (in.gcount() != block_size) {
		cerr << "Could not read a full template block for id " << template_id
			 << " from " << binary_path << " (got " << in.gcount() << " of "
			 << block_size << " bytes).\n";
		return false;
	}

	int bit_index = 0;
	for (int sq = 0; sq < 2; ++sq)
		for (int r = 0; r < order; ++r)
			for (int c = 0; c < order; ++c) {
				int byte_idx = bit_index / 8;
				int bit_pos  = bit_index % 8;
				TEMPLATE_F[sq][r][c] = (buffer[byte_idx] >> bit_pos) & 1;
				++bit_index;
			}

	return validateTemplate();
}

// Reads the template from a text file: 20 nonblank rows of 10 bits, square 0 first.
static bool readTemplateFile(const string& path) {
	ifstream in(path);
	if (!in) {
		cerr << "Cannot open template: " << path << "\n";
		return false;
	}

	vector<string> rows;
	string line;
	while (getline(in, line)) {
		string bits;
		for (char ch : line)
			if (ch == '0' || ch == '1') bits.push_back(ch);
		if (bits.empty()) continue;
		if ((int)bits.size() != order) {
			cerr << "Malformed template row: expected " << order
				 << " bits, got " << bits.size() << "\n";
			return false;
		}
		rows.push_back(bits);
	}

	if ((int)rows.size() != 2 * order) {
		cerr << "Template must contain exactly " << 2 * order
			 << " nonblank 10-bit rows; got " << rows.size() << "\n";
		return false;
	}

	for (int sq = 0; sq < 2; ++sq)
		for (int r = 0; r < order; ++r)
			for (int c = 0; c < order; ++c)
				TEMPLATE_F[sq][r][c] = rows[sq * order + r][c] - '0';

	return validateTemplate();
}

// Creates and returns <scratch_dir>/template_<ID or file stem>.
static string makeOutputDir(bool from_binary, int template_id, const string& template_path) {
	ostringstream name;
	if (from_binary) {
		name << "template_" << std::setw(4) << std::setfill('0') << template_id;
	} else {
		std::filesystem::path p(template_path);
		string stem = p.stem().string();
		name << "template_" << (stem.empty() ? string("adhoc") : stem);
	}
	std::filesystem::path dir = std::filesystem::path(scratch_dir) / name.str();
	std::error_code ec;
	std::filesystem::create_directories(dir, ec);
	if (ec)
		cerr << "WARNING: failed to create output directory " << dir.string() << ": " << ec.message() << "\n";
	return dir.string();
}

// Labels pinned in row 0 of square sq: walking the columns left to right, relational cells get 0,1,2,3 and non-relational cells 4..9.
// This fixes the class-preserving symbol relabeling, so every square the solver produces carries these labels.
static void buildRow0Labels(int sq, array<int8_t, 10>& labels) {
	int rel = 0, non = 4;
	for (int c = 0; c < order; ++c)
		labels[c] = (int8_t)(TEMPLATE_F[sq][0][c] ? rel++ : non++);
	if (rel != 4 || non != order) {
		cerr << "FATAL: row 0 of square " << sq << " is not of type 4^4.\n";
		exit(1);
	}
}

// The refinement constraints for the current template.
static void encodeTemplateConstraints(CaDiCaL::Solver& solver) {
	// Symbol class must match the template bit.
	for (int sq = 0; sq < 2; ++sq)
		for (int r = 0; r < order; ++r)
			for (int c = 0; c < order; ++c) {
				if (TEMPLATE_F[sq][r][c]) {
					for (int s = 4; s < order; ++s)
						solver.clause({-var(sq, r, c, s)});
				} else {
					for (int s = 0; s < 4; ++s)
						solver.clause({-var(sq, r, c, s)});
				}
			}

	// Parity: at every cell, [row<4] + [col<4] + [A relational] + [B relational] is even.
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

	// Pin row 0 of A and B to their normal form (see buildRow0Labels).
	for (int sq = 0; sq < 2; ++sq) {
		array<int8_t, 10> labels{};
		buildRow0Labels(sq, labels);
		for (int col = 0; col < order; ++col)
			solver.clause({var(sq, 0, col, labels[col])});
	}
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------
static long long g_raw_solutions_seen = 0;   // complete A squares that passed the full minimality check

static std::atomic<bool> g_search_running{false};

// DynamicAOnlyPolicy counters. Atomic because the heartbeat thread reads them while the search runs.
static std::atomic<long long> g_a_partial_calls{0};
static std::atomic<long long> g_a_partial_rejects{0};
static std::atomic<long long> g_a_full_models{0};
static std::atomic<long long> g_a_full_rejects{0};
static std::atomic<long long> g_a_sent_to_refinement{0};
static std::atomic<long long> g_a_symmetry_rejects{0};
static std::atomic<long long> g_a_bfeas_rejects{0};
static std::atomic<long long> g_a_bfeas_ns{0};
static std::atomic<long long> g_a_clauses_minimized{0};
static std::atomic<long long> g_a_clause_lits_before{0};
static std::atomic<long long> g_a_clause_lits_after{0};
static std::atomic<long long> g_a_notify_calls{0};   // calls of notify_assignment(), by far the hottest entry point
static std::atomic<long long> g_a_prefix_sum{0};     // known prefix length, summed over is_partial_solution() calls
static std::atomic<long long> g_pair_swap_rejects{0};
static std::atomic<long long> g_pair_stab_rejects{0};

static inline void bump(std::atomic<long long>& a, long long n = 1) {
	a.store(a.load(std::memory_order_relaxed) + n, std::memory_order_relaxed);
}

#if TRACK_TIME == 1
static std::atomic<long long> g_a_is_partial_ns{0};
static std::atomic<long long> g_a_minimize_ns{0};
static std::atomic<long long> g_a_operator_ns{0};

struct ScopedTimeAdd {
	std::atomic<long long>* acc;
	chrono::steady_clock::time_point t0;
	explicit ScopedTimeAdd(std::atomic<long long>* a) : acc(a), t0(chrono::steady_clock::now()) {}
	~ScopedTimeAdd() {
		acc->fetch_add(chrono::duration_cast<chrono::nanoseconds>(chrono::steady_clock::now() - t0).count(), std::memory_order_relaxed);
	}
};
#define DYN_TIME_SCOPE(acc) ScopedTimeAdd _dyn_time_scope(&(acc))
#else
#define DYN_TIME_SCOPE(acc) ((void)0)
#endif

// One-line progress report
static void printHeartbeat(std::ostream& os) {
	os << "[dyn] calls=" << g_a_partial_calls.load(std::memory_order_relaxed)
	   << " rejects=" << g_a_partial_rejects.load(std::memory_order_relaxed)
	   << " (sym=" << g_a_symmetry_rejects.load(std::memory_order_relaxed)
	   << " bfeas=" << g_a_bfeas_rejects.load(std::memory_order_relaxed) << ")"
	   << " full_models=" << g_a_full_models.load(std::memory_order_relaxed)
	   << " full_rejects=" << g_a_full_rejects.load(std::memory_order_relaxed)
	   << " sent=" << g_a_sent_to_refinement.load(std::memory_order_relaxed)
	   << " notify=" << g_a_notify_calls.load(std::memory_order_relaxed)
	   << " bfeas_time=" << (g_a_bfeas_ns.load(std::memory_order_relaxed) / 1e9) << "s"
#if TRACK_TIME == 1
	   << " is_partial_time=" << (g_a_is_partial_ns.load(std::memory_order_relaxed) / 1e9) << "s"
	   << " operator_time=" << (g_a_operator_ns.load(std::memory_order_relaxed) / 1e9) << "s"
#endif
	   << "\n";
}

static void printRejectionSummary(std::ostream& os) {
	os << "\n----- Rejection sources -----\n";
	os << "  symmetry (non-minimal A):     " << g_a_symmetry_rejects.load(std::memory_order_relaxed) << "\n";
	os << "  B-infeasible (no cover left): " << g_a_bfeas_rejects.load(std::memory_order_relaxed) << "\n";
	os << "  B-feasibility check time:     " << (g_a_bfeas_ns.load(std::memory_order_relaxed) / 1e9) << "s\n";
	long long n = g_a_clauses_minimized.load(std::memory_order_relaxed);
	long long b = g_a_clause_lits_before.load(std::memory_order_relaxed);
	long long a = g_a_clause_lits_after.load(std::memory_order_relaxed);
	os << "  blocking clauses minimized:   " << n;
	if (n) os << "  (" << ((double)b / n) << " -> " << ((double)a / n) << " literals)";
	os << "\n";
	os << "  pair-level rejects (swap):    " << g_pair_swap_rejects.load(std::memory_order_relaxed) << "\n";
	os << "  pair-level rejects (A-stab):  " << g_pair_stab_rejects.load(std::memory_order_relaxed) << "\n";
	os << "  pairs examined by filter:     " << g_pair_filter_examined << "\n";
	os << "notify_assignment calls: " << g_a_notify_calls.load(std::memory_order_relaxed) << "\n";
}

// Prints a progress line every interval_s seconds while g_search_running is set.
static void searchHeartbeat(double interval_s = 10.0) {
	using namespace std::chrono;
	auto last = steady_clock::now();
	while (g_search_running.load(std::memory_order_relaxed)) {
		std::this_thread::sleep_for(milliseconds(100));   // short sleeps so the thread stops promptly when the search ends
		if (!g_search_running.load(std::memory_order_relaxed)) break;
		if (duration<double>(steady_clock::now() - last).count() < interval_s) continue;
		last = steady_clock::now();
		printHeartbeat(cerr);
		cerr.flush();
	}
}

// ---------------------------------------------------------------------------
// Aut(T)
// ---------------------------------------------------------------------------

// A symmetry of the pair representation, as a map from output cells to source cells: with `transpose`, output (r,c) reads source (rowMap[c], colMap[r]); otherwise (rowMap[r], colMap[c])
// With `swapSquares`, output A and B read from source B and A. mappedCell[i] caches the source flat cell read by canonical output cell i.
// Every Generator preserves the template, so it maps refinements to refinements.
struct Generator {
	bool transpose = false;
	bool swapSquares = false;
	array<int8_t, 10> rowMap;
	array<int8_t, 10> colMap;
	std::array<uint8_t, NCELLS> mappedCell{};
};

static inline int mappedFlatCell(const Generator& g, int outR, int outC) {
	int r0 = g.transpose ? g.rowMap[outC] : g.rowMap[outR];
	int c0 = g.transpose ? g.colMap[outR] : g.colMap[outC];
	return r0 * order + c0;
}

static void fillMappedCell(Generator& g) {
	for (int idx = 0; idx < NCELLS; ++idx) {
		auto [r, c] = canonicalCells[idx];
		g.mappedCell[idx] = static_cast<uint8_t>(mappedFlatCell(g, r, c));
	}
}

// An element of Aut(T) as decoded from nauty: source -> destination maps
struct TemplateAuto {
	bool transpose = false;
	bool swap_squares = false;
	array<int, 10> row_dest{};
	array<int, 10> col_dest{};
};

static vector<TemplateAuto> g_template_auts;   // the full verified group, identity included
static constexpr size_t MAX_TEMPLATE_AUT_GROUP = 200000;

static TemplateAuto fromDecodedTemplateAuto(const TemplateAutoNS::DecodedTemplateAuto& d) {
	TemplateAuto a;
	a.transpose = d.transpose;
	a.swap_squares = d.swap_squares;
	a.row_dest = d.row_dest;
	a.col_dest = d.col_dest;
	return a;
}

// Inverts a permutation of 0..9; exits if p is not one
template <typename T>
static void inversePermutation10(const array<int, 10>& p, array<T, 10>& inv) {
	array<char, 10> seen{};
	for (int i = 0; i < 10; ++i) {
		if (p[i] < 0 || p[i] >= 10 || seen[p[i]]) {
			cerr << "FATAL: malformed template automorphism.\n";
			exit(1);
		}
		inv[p[i]] = static_cast<T>(i);
		seen[p[i]] = 1;
	}
}

static bool templateAutoIsIdentity(const TemplateAuto& a) {
	if (a.transpose || a.swap_squares) return false;
	for (int i = 0; i < 10; ++i)
		if (a.row_dest[i] != i || a.col_dest[i] != i) return false;
	return true;
}

// Checks directly against the binary matrices that `a` maps T to itself
static bool preservesTemplate(const TemplateAuto& a) {
	array<int, 10> row_inv{}, col_inv{};
	inversePermutation10(a.row_dest, row_inv);
	inversePermutation10(a.col_dest, col_inv);

	for (int r = 0; r < order; ++r)
		for (int c = 0; c < order; ++c) {
			int sr, sc;
			if (!a.transpose) {
				sr = row_inv[r];
				sc = col_inv[c];
			} else {
				sr = row_inv[c];
				sc = col_inv[r];
			}

			int source0 = a.swap_squares ? 1 : 0;
			int source1 = a.swap_squares ? 0 : 1;
			if (TEMPLATE_F[0][r][c] != TEMPLATE_F[source0][sr][sc] ||
				TEMPLATE_F[1][r][c] != TEMPLATE_F[source1][sr][sc])
				return false;
		}
	return true;
}

// Generators map output cells to source cells, while the decoded automorphism stores source -> destination, so the permutations are inverted
static Generator templateAutoAsGenerator(const TemplateAuto& a) {
	Generator g;
	g.transpose = a.transpose;
	g.swapSquares = a.swap_squares;
	inversePermutation10(a.row_dest, g.rowMap);
	inversePermutation10(a.col_dest, g.colMap);
	fillMappedCell(g);
	return g;
}

// Computes Aut(T) with nauty into g_template_auts. `text_path` is the template's text file, or empty if it came from templates.bin. 
// The automorphism module parses the template with its own reader and the two results are cross-checked.
static void loadTemplateAutomorphisms(const string& text_path, const string& binary_path, int template_id) {
	int F0[10][10], F1[10][10];
	const bool read_ok = text_path.empty() ? TemplateAutoNS::read_template_binary(binary_path, template_id, F0, F1) : TemplateAutoNS::read_template(text_path, F0, F1);
	if (!read_ok) {
		cerr << "FATAL: automorphism reader rejected template.\n";
		exit(1);
	}

	for (int r = 0; r < order; ++r)
		for (int c = 0; c < order; ++c)
			if (F0[r][c] != TEMPLATE_F[0][r][c] || F1[r][c] != TEMPLATE_F[1][r][c]) {
				cerr << "FATAL: template readers disagree.\n";
				exit(1);
			}

	int lambda2 = 0, lambda3 = 0;
	if (!TemplateAutoNS::detect_lambda(F0, "F0", lambda2) ||
		!TemplateAutoNS::detect_lambda(F1, "F1", lambda3) ||
		lambda2 != 4 || lambda3 != 4) {
		cerr << "FATAL: template is not type 4^4.\n";
		exit(1);
	}

	TemplateAutoNS::BuiltGraph graph = TemplateAutoNS::build_graph(F0, F1);
	int lab[TemplateAutoNS::N_NAUTY], ptn[TemplateAutoNS::N_NAUTY], orbits[TemplateAutoNS::N_NAUTY];
	TemplateAutoNS::build_partition(4, 4, lab, ptn);

	DEFAULTOPTIONS_SPARSEGRAPH(options);
	options.getcanon = TRUE;
	options.defaultptn = FALSE;
	options.writeautoms = FALSE;
	options.writemarkers = FALSE;
	options.userautomproc = TemplateAutoNS::userautomproc;

	statsblk stats;
	sparsegraph canon_sg;
	SG_INIT(canon_sg);
	TemplateAutoNS::g_generators.clear();
	sparsenauty(&graph.sg, lab, ptn, orbits, &options, &stats, &canon_sg);

	if (stats.grpsize2 != 0) {
		cerr << "FATAL: template automorphism group has a 10^k factor; refusing incomplete closure.\n";
		exit(1);
	}

	long long expected_order = static_cast<long long>(stats.grpsize1);
	vector<TemplateAutoNS::Perm> generators(TemplateAutoNS::g_generators.begin(), TemplateAutoNS::g_generators.end());
	vector<TemplateAutoNS::Perm> full_group = TemplateAutoNS::close_group(generators, graph, expected_order, MAX_TEMPLATE_AUT_GROUP);
	if (full_group.size() != static_cast<size_t>(expected_order)) {
		cerr << "FATAL: template automorphism group closure mismatch.\n";
		exit(1);
	}

	// Decode every element and verify it against the binary matrices, so neither nauty's encoding nor the decode convention is trusted alone.
	g_template_auts.clear();
	for (const TemplateAutoNS::Perm& p : full_group) {
		TemplateAuto a = fromDecodedTemplateAuto(TemplateAutoNS::decode(p));
		if (!preservesTemplate(a)) {
			cerr << "FATAL: decoded template automorphism failed direct verification.\n";
			exit(1);
		}
		g_template_auts.push_back(a);
	}

	cout << "Template Aut(T) order (verified): " << g_template_auts.size() << "\n";
}

// ---------------------------------------------------------------------------
// CNF encoding
// ---------------------------------------------------------------------------
static int g_next_aux_var = 0;   // last auxiliary variable handed out; set in buildFormula()
static int newAuxVar() { return ++g_next_aux_var; }

// Exactly one literal of lits is true: sequential-counter at-most-one (n-1 auxiliary variables) plus one at-least-one clause.
void encodeExactlyOneSinz(CaDiCaL::Solver& solver, const vector<int>& lits) {
	int n = (int)lits.size();
	if (n == 1) {
		solver.clause({lits[0]});
		return;
	}
	vector<int> s(n - 1);
	for (int i = 0; i < n - 1; ++i) s[i] = newAuxVar();
	solver.clause({-lits[0], s[0]});
	for (int i = 1; i < n - 1; ++i) {
		solver.clause({-lits[i], s[i]});
		solver.clause({-s[i - 1], s[i]});
		solver.clause({-lits[i], -s[i - 1]});
	}
	solver.clause({-lits[n - 1], -s[n - 2]});
	solver.clause(lits);
}

// Enforces seq_a <=_lex seq_b. eq_t means "positions 0..t are all equal", so the first difference is forced to go in the right direction.
static void lexLeq(CaDiCaL::Solver& solver, const vector<vector<int>>& seq_a, const vector<vector<int>>& seq_b) {
	int n = (int)seq_a.size();
	int eq_prev = 0;

	for (int t = 0; t < n; ++t) {
		const vector<int>& a_cell = seq_a[t];
		const vector<int>& b_cell = seq_b[t];

		// if all earlier positions are equal, a must not exceed b here
		for (int s = 0; s < order; ++s)
			for (int s2 = 0; s2 < s; ++s2) {
				if (eq_prev)
					solver.clause({-eq_prev, -a_cell[s], -b_cell[s2]});
				else
					solver.clause({-a_cell[s], -b_cell[s2]});
			}

		if (t == n - 1) break;

		int eq_t = newAuxVar();
		if (eq_prev) solver.clause({-eq_t, eq_prev});

		for (int s = 0; s < order; ++s) {
			solver.clause({-eq_t, -a_cell[s], b_cell[s]});
			solver.clause({-eq_t, -b_cell[s], a_cell[s]});

			if (eq_prev)
				solver.clause({-eq_prev, -a_cell[s], -b_cell[s], eq_t});
			else
				solver.clause({-a_cell[s], -b_cell[s], eq_t});
		}

		eq_prev = eq_t;
	}
}

// Latin square axioms for square sq: one symbol per cell, and each symbol exactly once per row and per column.
void encodeLatinSquare(CaDiCaL::Solver& solver, int sq) {
	for (int r = 0; r < order; ++r)
		for (int c = 0; c < order; ++c) {
			vector<int> lits(order);
			for (int s = 0; s < order; ++s)
				lits[s] = var(sq, r, c, s);
			encodeExactlyOneSinz(solver, lits);
		}
	for (int r = 0; r < order; ++r)
		for (int s = 0; s < order; ++s) {
			vector<int> lits(order);
			for (int c = 0; c < order; ++c)
				lits[c] = var(sq, r, c, s);
			encodeExactlyOneSinz(solver, lits);
		}
	for (int c = 0; c < order; ++c)
		for (int s = 0; s < order; ++s) {
			vector<int> lits(order);
			for (int r = 0; r < order; ++r)
				lits[r] = var(sq, r, c, s);
			encodeExactlyOneSinz(solver, lits);
		}
}

// A and B are orthogonal iff the auxiliary square Z with Z(i,l) = k whenever (A(i,j), B(i,j)) = (k,l) is Latin: then every ordered symbol pair occurs exactly once.
void encodeOrthogonality(CaDiCaL::Solver& solver) {
	encodeLatinSquare(solver, 2);
	for (int i = 0; i < order; ++i)
		for (int j = 0; j < order; ++j)
			for (int k2 = 0; k2 < order; ++k2)
				for (int l = 0; l < order; ++l) {
					int a = var(0, i, j, k2), b = var(1, i, j, l), z = var(2, i, l, k2);
					solver.clause({-a, -b, z});
					solver.clause({-z, -b, a});
					solver.clause({-z, -a, b});
				}
}

static vector<int> cellLits(int sq, int r, int c) {
	vector<int> lits(order);
	for (int s = 0; s < order; ++s)
		lits[s] = var(sq, r, c, s);
	return lits;
}

// Lex-leader clauses (A,B) <= sigma(g(A,B)) for the elements of Aut(T) whose renormalization sigma is constant, which are the non-transposing elements with row_inv[0] == 0 (they fix row 0 setwise). 
// For the others sigma depends on the assignment and is left to DynamicAOnlyPolicy and pairLevelAccept(). 
static void encodeTemplateAutomorphismSymmetry(CaDiCaL::Solver& solver) {
	array<int8_t, 10> row0Label[2];
	buildRow0Labels(0, row0Label[0]);
	buildRow0Labels(1, row0Label[1]);

	vector<vector<int>> original;
	original.reserve(2 * NCELLS);
	for (int sq = 0; sq < 2; ++sq)
		for (auto [r, c] : canonicalCells)
			original.push_back(cellLits(sq, r, c));

	size_t encoded = 0, skipped = 0;
	for (const TemplateAuto& a : g_template_auts) {
		if (templateAutoIsIdentity(a)) continue;

		array<int, 10> row_inv{}, col_inv{};
		inversePermutation10(a.row_dest, row_inv);
		inversePermutation10(a.col_dest, col_inv);

		if (a.transpose || row_inv[0] != 0) { ++skipped; continue; }

		// sigmaInv[sq][s] = the source symbol whose renormalized image is s. Image cell (0,c) of square sq reads source square src_sq at
		// (0, col_inv[c]), which is pinned to row0Label[src_sq][col_inv[c]], and must end up holding row0Label[sq][c].
		array<int8_t, 10> sigmaInv[2];
		bool ok = true;
		for (int sq = 0; sq < 2 && ok; ++sq) {
			sigmaInv[sq].fill((int8_t)-1);
			int src_sq = a.swap_squares ? 1 - sq : sq;
			for (int c = 0; c < order; ++c) {
				int srcVal = row0Label[src_sq][col_inv[c]];
				int dstVal = row0Label[sq][c];
				if (symClass(srcVal) != symClass(dstVal)) { ok = false; break; }
				sigmaInv[sq][dstVal] = (int8_t)srcVal;
			}
			for (int s = 0; s < order && ok; ++s)
				if (sigmaInv[sq][s] < 0) ok = false;
		}
		if (!ok) {
			cerr << "FATAL: static row-0 renormalization is not a class-preserving bijection.\n";
			exit(1);
		}

		vector<vector<int>> transformed;
		transformed.reserve(2 * NCELLS);
		for (int sq = 0; sq < 2; ++sq) {
			int src_sq = a.swap_squares ? 1 - sq : sq;
			for (auto [r, c] : canonicalCells) {
				int sr = row_inv[r], sc = col_inv[c];
				vector<int> lits(order);
				// "renormalized image at (r,c) equals s" is the literal "source cell holds sigma^{-1}(s)"
				for (int s = 0; s < order; ++s)
					lits[s] = var(src_sq, sr, sc, sigmaInv[sq][s]);
				transformed.push_back(std::move(lits));
			}
		}

		lexLeq(solver, original, transformed);
		++encoded;
	}

	cerr << "[setup] Static Aut(T) lex-leaders: " << encoded << " encoded, " << skipped << " deferred to dynamic pruning (assignment-dependent renormalization)\n";
}

// Assembles the CNF
void buildFormula(CaDiCaL::Solver& solver) {
	int total_base_vars = 3 * order * order * order;
	solver.declare_more_variables(total_base_vars);
	g_next_aux_var = total_base_vars;

	encodeLatinSquare(solver, 0);
	encodeLatinSquare(solver, 1);
	encodeOrthogonality(solver);
	encodeTemplateConstraints(solver);
	encodeTemplateAutomorphismSymmetry(solver);
}

// ---------------------------------------------------------------------------
// Generators for the dynamic (A-only) layer
// ---------------------------------------------------------------------------
static array<int8_t, 10> g_row0LabelA{};
static array<int8_t, 10> g_row0LabelB{};

// A non-swapping element whose renormalization sigma_g depends on A. Image cell (0,c) reads A at flat cell srcRow0[c], and sigma_g must send that value to g_row0LabelA[c]. 
// All ten srcRow0 cells lie in one row (or column, when transposing) of A, so sigma_g is known once that line is assigned.
struct AOnlyGen {
	Generator g;
	int autIdx = -1;               // position in g_template_auts; the element id used in dynamic_clauses_<ID>.bin
	array<uint8_t, 10> srcRow0{};
};

static vector<AOnlyGen> g_aOnlyGens;

static void setupAOnlyGenerators() {
	buildRow0Labels(0, g_row0LabelA);
	buildRow0Labels(1, g_row0LabelB);

	g_aOnlyGens.clear();
	size_t constant_sigma = 0;
	for (size_t ai = 0; ai < g_template_auts.size(); ++ai) {
		const TemplateAuto& a = g_template_auts[ai];
		// A square swap would make the image of A read from B, which is not observed here.
		if (templateAutoIsIdentity(a) || a.swap_squares) continue;

		AOnlyGen ag;
		ag.g = templateAutoAsGenerator(a);
		ag.autIdx = (int)ai;
		bool fixesRow0 = true;
		for (int c = 0; c < order; ++c) {
			int flat = mappedFlatCell(ag.g, 0, c);
			ag.srcRow0[c] = (uint8_t)flat;
			if (flat / order != 0) fixesRow0 = false;
		}

		// A constant sigma is already encoded in the CNF, so the dynamic scan could never reject on it.
		if (fixesRow0) { ++constant_sigma; continue; }
		g_aOnlyGens.push_back(ag);
	}

	cerr << "A-only dynamic generators: " << g_aOnlyGens.size() << " (" << constant_sigma << " more with a constant renormalization are in the CNF instead)\n";

	for (size_t i = 0; i < g_aOnlyGens.size(); ++i) {
		const AOnlyGen& ag = g_aOnlyGens[i];
		int movedCells = 0;
		for (int idx = 0; idx < NCELLS; ++idx) {
			auto [r, c] = canonicalCells[idx];
			if (ag.g.mappedCell[idx] != r * order + c) ++movedCells;
		}
		cerr << "  gen[" << i << "] transpose=" << (ag.g.transpose ? 1 : 0)
			 << " cells_moved=" << movedCells
			 << " sigma=runtime(needs " << (ag.g.transpose ? "column " : "row ")
			 << (ag.g.transpose ? (ag.srcRow0[0] % order) : (ag.srcRow0[0] / order)) << " of A)\n";
	}
}

// ---------------------------------------------------------------------------
// Pair-level symmetry filter
//
// Applies every non-identity element of Aut(T) to a finished (A,B) pair, by the lex-leader test in A-then-B order.
// It is needed because the SAT model's B is only an existential witness, not the B's the refinement step enumerates: 
// 		elements that swap the squares or that fix A while moving B can only be applied here.
//
// The leader satisfies (A,B) <= (A',B') for every element, hence A <= A' for every non-swapping one, so it is never discarded upstream.
//
// Both sides of a comparison must be row-0 normalized. buildPairSigma() makes the image so; normalizeRow0() does the same for the original, which the refinement engine does not guarantee for B.
// ---------------------------------------------------------------------------
struct PairGen {
	Generator g;
	array<uint8_t, 10> srcRow0{};  // flat source cell feeding image cell (0,c)
};

static vector<PairGen> g_pairGens;

static void setupPairGenerators() {
	g_pairGens.clear();
	for (const TemplateAuto& a : g_template_auts) {
		if (templateAutoIsIdentity(a)) continue;
		PairGen pg;
		pg.g = templateAutoAsGenerator(a);
		for (int c = 0; c < order; ++c)
			pg.srcRow0[c] = (uint8_t)mappedFlatCell(pg.g, 0, c);
		g_pairGens.push_back(pg);
	}
	cerr << "Pair-level Aut(T) elements: " << g_pairGens.size() << "\n";
}

// Builds the relabeling sigma that maps the values `src` holds at cells srcRow0[0..9] onto the pinned row-0 labels. With srcRow0 = row 0 itself this normalizes a square; 
// with srcRow0 = the cells feeding row 0 of an image it is sigma_g. Returns false if those values are not distinct.
static inline bool buildPairSigma(const uint8_t* src, const array<uint8_t, 10>& srcRow0, const array<int8_t, 10>& labels, array<int8_t, 10>& sigma) {
	sigma.fill((int8_t)-1);
	for (int c = 0; c < order; ++c) {
		int v = src[srcRow0[c]];
		if (v < 0 || v >= order || sigma[v] >= 0) return false;
		sigma[v] = labels[c];
	}
	return true;
}

// srcRow0 table of the identity map: cells (0,0)..(0,9).
static array<uint8_t, 10> g_row0Cells = [] {
	array<uint8_t, 10> a{};
	for (int c = 0; c < order; ++c) a[c] = (uint8_t)c;
	return a;
}();

// Relabels a grid into the row-0 normal form pinned by encodeTemplateConstraints(). A comes from the SAT symbols and is already normalized. 
// B comes from linesToGrid(), where a symbol is just the position of its line in the cover, so it must be normalized before it is compared with a normalized image.
static inline bool normalizeRow0(uint8_t X[NCELLS], const array<int8_t, 10>& labels) {
	array<int8_t, 10> sigma{};
	if (!buildPairSigma(X, g_row0Cells, labels, sigma)) return false;
	for (int p = 0; p < NCELLS; ++p) X[p] = (uint8_t)sigma[X[p]];
	return true;
}

// Returns true iff (A,B) is <= its renormalized image under every non-identity element of Aut(T).
static bool pairLevelAccept(const uint8_t Araw[NCELLS], const uint8_t Braw[NCELLS]) {
	uint8_t A[NCELLS], B[NCELLS];
	memcpy(A, Araw, NCELLS);
	memcpy(B, Braw, NCELLS);

	if (!normalizeRow0(A, g_row0LabelA) || !normalizeRow0(B, g_row0LabelB)) {
		cerr << "FATAL: pair from the refinement engine has a degenerate row 0.\n";
		exit(1);
	}

	// A is built from SAT symbols, so normalizing it must change nothing. If it does, the A-only layer compares against the wrong slice as well.
	if (memcmp(A, Araw, NCELLS) != 0) {
		cerr << "FATAL: A handed to the pair filter is not row-0 normalized.\n";
		exit(1);
	}

	array<int8_t, 10> sigmaA{}, sigmaB{};

	for (const PairGen& pg : g_pairGens) {
		const uint8_t* SA = pg.g.swapSquares ? B : A;  // supplies the image's A
		const uint8_t* SB = pg.g.swapSquares ? A : B;  // supplies the image's B

		if (!buildPairSigma(SA, pg.srcRow0, g_row0LabelA, sigmaA)) continue;
		if (!buildPairSigma(SB, pg.srcRow0, g_row0LabelB, sigmaB)) continue;

		// A first, then B, in canonical order
		int cmp = 0;
		for (int idx = 0; idx < NCELLS && cmp == 0; ++idx) {
			int img = sigmaA[SA[pg.g.mappedCell[idx]]];
			int own = A[g_canonPoint[idx]];
			if (img < own) cmp = -1;
			else if (img > own) cmp = +1;
		}
		for (int idx = 0; idx < NCELLS && cmp == 0; ++idx) {
			int img = sigmaB[SB[pg.g.mappedCell[idx]]];
			int own = B[g_canonPoint[idx]];
			if (img < own) cmp = -1;
			else if (img > own) cmp = +1;
		}

		if (cmp < 0) {
			if (pg.g.swapSquares) g_pair_swap_rejects.fetch_add(1, std::memory_order_relaxed);
			else g_pair_stab_rejects.fetch_add(1, std::memory_order_relaxed);
			return false;
		}
	}
	return true;
}

// ---------------------------------------------------------------------------
// dynamic_clauses_<ID>.bin: log of automorphism-justified blocks. All multi-byte fields are little-endian.
//
// HEADER
//   4 bytes  magic "DYNC"
//   1 byte   format version (1)
//   1 byte   order (10)
//   1 byte   idBits = bits per automorphism element id = max(1, ceil(log2(E)))
//   1 byte   reserved (0)
//   4 bytes  uint32 E, the number of elements of the verified Aut(T), identity included
//   4 bytes  int32 template id (-1 for a text template)
//   E x 11 bytes, element i (id = position in this list):
//       1 byte  flags: bit0 transpose, bit1 swap_squares, bit2 identity
//       5 bytes row_dest[0..9], 4-bit nibbles, low nibble first (source row -> destination row)
//       5 bytes col_dest[0..9], same packing
//
// RECORDS until EOF. One record = one block justified by one element. A record is a little-endian bit string (first field in the lowest bits), zero-padded to a whole byte:
//   1 bit        mode: 0 = cell list, 1 = cell bitmask
//   idBits       automorphism element id
//   mode 0:      7 bits N (number of cells), then N x 7 bits flat cell numbers p = r*10+c, ascending
//   mode 1:      100 bits, bit p set iff cell p is in the record (N = popcount)
//   N x 4 bits   symbol held by each cell, in ascending cell order
// The smaller mode is used (list up to 14 cells, bitmask from 15). Decoded, a record is the positive A literals var(0,r,c,s) = p*10 + s + 1 that the
// minimality comparison read, as they stood before the element was applied; their negation is a clause implied by the formula.
//
// A record is written for every rejection by the dynamic A-only scan (partial rejections in is_partial_solution(), full-grid rejections in operator()). 
// DynamicClauseDedup drops most repeats and a run killed mid-write can leave a truncated last record, which readers should discard.
// ---------------------------------------------------------------------------
static std::atomic<long long> g_dynamic_clause_lines{0};
static std::atomic<long long> g_dynamic_clause_bytes{0};
static std::atomic<long long> g_dynamic_clause_dups{0};
static int g_dynamic_id_bits = 1;

// ---------------------------------------------------------------------------
// Write-time de-duplication of records with bounded memory.
//
// Records are canonical, so equal records have equal bytes.
// The table starts at 64Ki slots and doubles up to DYNAMIC_DEDUP_MAX_MB (default 512, about 23 million records; 0 disables de-duplication).
// ---------------------------------------------------------------------------
#ifndef DYNAMIC_DEDUP_MAX_MB
#define DYNAMIC_DEDUP_MAX_MB 512
#endif

struct DynFingerprint {
	uint64_t lo = 0, hi = 0;
	bool empty() const { return lo == 0 && hi == 0; }
	bool operator==(const DynFingerprint& o) const { return lo == o.lo && hi == o.hi; }
};

struct DynamicClauseDedup {
	std::vector<DynFingerprint> slots;   // power-of-two size once allocated
	size_t used = 0;
	size_t maxSlots = 0;                 // power of two, 0 = de-duplication disabled
	bool full = false;                   // the cap stopped at least one fingerprint from being remembered

	DynamicClauseDedup() {
		const unsigned long long budget = (unsigned long long)DYNAMIC_DEDUP_MAX_MB << 20;
		if (budget >= 2 * sizeof(DynFingerprint)) {
			size_t n = 1;
			while ((unsigned long long)n * 2 * sizeof(DynFingerprint) <= budget) n *= 2;
			maxSlots = n;
		}
	}

	static size_t initialSlots(size_t cap) { return cap < ((size_t)1 << 16) ? cap : ((size_t)1 << 16); }

	// Inserts a fingerprint known to be absent into a table with room.
	static void insertAbsent(std::vector<DynFingerprint>& t, const DynFingerprint& fp) {
		const size_t mask = t.size() - 1;
		size_t i = (size_t)fp.lo & mask;
		while (!t[i].empty()) i = (i + 1) & mask;
		t[i] = fp;
	}

	// Returns true if fp was already recorded (the caller skips the record); otherwise remembers it if there is room and returns false.
	bool seenOrInsert(DynFingerprint fp) {
		if (maxSlots == 0) return false;
		if (fp.empty()) fp.lo = 1;   // all-zero is the empty marker
		if (slots.empty()) slots.assign(initialSlots(maxSlots), DynFingerprint{});

		size_t mask = slots.size() - 1;
		size_t i = (size_t)fp.lo & mask;
		while (!slots[i].empty()) {
			if (slots[i] == fp) return true;
			i = (i + 1) & mask;
		}

		if ((used + 1) * 10 > slots.size() * 7) {   // would exceed 70% load
			if (slots.size() * 2 > maxSlots) { full = true; return false; }
			std::vector<DynFingerprint> bigger(slots.size() * 2, DynFingerprint{});
			for (const DynFingerprint& v : slots) if (!v.empty()) insertAbsent(bigger, v);
			slots.swap(bigger);
			insertAbsent(slots, fp);
		} else {
			slots[i] = fp;
		}
		++used;
		return false;
	}

	size_t bytes() const { return slots.capacity() * sizeof(DynFingerprint); }
};

static inline DynFingerprint dynFingerprint(const std::string& rec) {
	DynFingerprint f;
	f.lo = es_wyhash(rec.data(), rec.size(), 0x2545f4914f6cdd1dULL);
	f.hi = es_wyhash(rec.data(), rec.size(), 0x9e6c63d0876a9a99ULL);
	return f;
}

static DynamicClauseDedup g_dynamicDedup;

// Appends the low n bits (n <= 57) of v to `out` at bit position `bitpos`, LSB first, growing `out` as needed.
static inline void dynPutBits(std::string& out, size_t& bitpos, uint64_t v, int n) {
	if (n <= 0) return;
	v &= (n >= 64) ? ~0ULL : ((1ULL << n) - 1);
	const size_t need = (bitpos + n + 7) / 8;
	if (out.size() < need) out.resize(need, '\0');
	size_t byte = bitpos >> 3;
	int off = (int)(bitpos & 7);
	int left = n;
	while (left > 0) {
		out[byte] = (char)((uint8_t)out[byte] | (uint8_t)((v << off) & 0xFF));
		int took = 8 - off; if (took > left) took = left;
		v >>= took; left -= took; ++byte; off = 0;
	}
	bitpos += n;
}

static_assert(NCELLS <= 100, "dynamic_clauses record format supports at most 100 cells");
static_assert(order <= 16, "dynamic_clauses record format stores symbols in 4 bits");

// Encodes one record into `out`. `reason` is a bitmask over flat cells; cells with val < 0 are dropped.
static void encodeDynamicClauseRecord(std::string& out, int idBits, int elemId, const int8_t* val, __uint128_t reason) {
	int cells[NCELLS]; int n = 0;
	__uint128_t mask = 0;
	for (int p = 0; p < NCELLS; ++p)
		if (((reason >> p) & 1) && val[p] >= 0) { cells[n++] = p; mask |= (__uint128_t)1 << p; }

	assert(elemId >= 0 && (idBits >= 31 || elemId < (1 << idBits)));   // otherwise the id would be truncated
	out.clear();
	size_t bp = 0;
	const bool useMask = n >= 15;   // list costs 7 + 7n bits, mask costs 100 bits
	dynPutBits(out, bp, useMask ? 1 : 0, 1);
	dynPutBits(out, bp, (uint64_t)elemId, idBits);
	if (useMask) {
		dynPutBits(out, bp, (uint64_t)(mask & (((__uint128_t)1 << 50) - 1)), 50);
		dynPutBits(out, bp, (uint64_t)(mask >> 50), 50);
	} else {
		dynPutBits(out, bp, (uint64_t)n, 7);
		for (int i = 0; i < n; ++i) dynPutBits(out, bp, (uint64_t)cells[i], 7);
	}
	for (int i = 0; i < n; ++i) dynPutBits(out, bp, (uint64_t)val[cells[i]], 4);
}

static void dynPutLE(std::string& o, uint64_t v, int bytes) {
	for (int i = 0; i < bytes; ++i) o.push_back((char)((v >> (8 * i)) & 0xFF));
}

static void writeDynamicClausesHeader() {
#if WRITE_DYNAMIC_CLAUSES == 1
	if (!dynamic_clauses_file.is_open()) return;
	const size_t E = g_template_auts.size();
	g_dynamic_id_bits = 1;
	while ((1ULL << g_dynamic_id_bits) < E) ++g_dynamic_id_bits;

	std::string h;
	h += "DYNC";
	h.push_back((char)1);                        // version
	h.push_back((char)order);
	h.push_back((char)g_dynamic_id_bits);
	h.push_back((char)0);                        // reserved
	dynPutLE(h, (uint64_t)E, 4);
	dynPutLE(h, (uint64_t)(uint32_t)(int32_t)TEMPLATE_ID, 4);
	for (const TemplateAuto& a : g_template_auts) {
		uint8_t flags = (uint8_t)((a.transpose ? 1 : 0) | (a.swap_squares ? 2 : 0) | (templateAutoIsIdentity(a) ? 4 : 0));
		h.push_back((char)flags);
		for (int which = 0; which < 2; ++which) {
			const array<int, 10>& d = which ? a.col_dest : a.row_dest;
			for (int k = 0; k < 5; ++k)
				h.push_back((char)((d[2 * k] & 0xF) | ((d[2 * k + 1] & 0xF) << 4)));
		}
	}
	dynamic_clauses_file.write(h.data(), (std::streamsize)h.size());
	dynamic_clauses_file.flush();
	g_dynamic_clause_bytes.fetch_add((long long)h.size(), std::memory_order_relaxed);
#endif
}

// ---------------------------------------------------------------------------
// DynamicAOnlyPolicy: propagator policy, it observes only A while B is completed existentially by the formula and enumerated separately by the refinement step. 
// With only_neg, blocking a complete assignment negates its positive observed literals, which removes only A.
//
//   notify_assignment  Called for every assignment and backtrack of an A variable. Maintains val[] (per-symbol cell sets) 
//                      and for each completed symbol transversal its candidate-line index (cand_hash_A).
//   is_partial_solution Rejects a partial A if (i) bFeasible() fails: the completed transversals leave fewer than `order` B lines; or (ii) findRenormalizedWitness() finds
//                      a generator whose renormalized image is lexicographically smaller on the assigned prefix.
//   minimize           Cuts the blocking clause down to the cells that justified the rejection, so it prunes a whole family of A's.
//   operator()         At a complete A: repeats the minimality check on the full grid, passes A to solve_partial_solution(), and returns false so A is blocked either way.
//
// ---------------------------------------------------------------------------
struct DynamicAOnlyPolicy {
	// Symbol of A at each flat cell, -1 if unassigned.
	mutable array<int8_t, NCELLS> val{};

	// Bit i set iff val[g_canonPoint[i]] >= 0, i.e. assigned cells in canonical order. Always mirrors val[], assigned prefix is the number of trailing one bits.
	mutable __uint128_t canon_assigned_ = 0; //(Bits 100..127 stay zero)

	// Cells holding each symbol; a symbol whose ten cells are all assigned is a completed transversal, looked up in cand_hash_A.
	mutable __uint128_t sym_points[order] = {};
	mutable int sym_cnt[order] = {};
	mutable int sym_A_idx[order];      // candidate-line index of a completed transversal, -1 if none or incomplete
	mutable int complete_count = 0;    // completed transversals
	mutable int candidate_count = 0;   // completed transversals that are candidate lines

	// Why the last rejection happened, so minimize() can shorten the clause.
	enum class RejectKind { NONE, SYMMETRY, B_INFEASIBLE };
	mutable RejectKind last_reject_kind_ = RejectKind::NONE;
	mutable __uint128_t last_reason_points_ = 0;

	// Bumped whenever the set of completed transversals changes; caches the B-feasibility result across calls that leave it unchanged.
	mutable uint64_t transversal_version_ = 0;
	mutable uint64_t bfeas_version_ = ~0ULL;
	mutable bool bfeas_result_ = true;
	mutable __uint128_t bfeas_reason_ = 0;

	DynamicAOnlyPolicy() {
		val.fill((int8_t)-1);
		for (int s = 0; s < order; ++s) sym_A_idx[s] = -1;
	}

	// lit > 0: the variable became true; lit == 0: the assignment was retracted; lit < 0 (false) is ignored. A is exactly variables 1..order^3, so range checks that if variable belongs to A.
	void notify_assignment(int variable, int lit) const {
		if ((unsigned)(variable - 1) >= (unsigned)(order * order * order)) return;
		if (lit < 0) return;

		bump(g_a_notify_calls);

		const int point = g_varPoint[variable];
		const int s     = g_varSym[variable];
		val[point] = lit > 0 ? (int8_t)s : (int8_t)-1;
		{
			const __uint128_t cbit = (__uint128_t)1 << g_pointCanon[point];
			if (lit > 0) canon_assigned_ |= cbit;
			else         canon_assigned_ &= ~cbit;
		}

		const __uint128_t bit = (__uint128_t)1 << point;
		const bool was_complete = (sym_cnt[s] == order);

		if (lit > 0) {
			if (!(sym_points[s] & bit)) {
				sym_points[s] |= bit;
				++sym_cnt[s];
			}
		} else {
			if (sym_points[s] & bit) {
				sym_points[s] &= ~bit;
				--sym_cnt[s];
			}
		}

		const bool now_complete = (sym_cnt[s] == order);
		if (now_complete && !was_complete) {
			++complete_count;
			++transversal_version_;
			auto it = cand_hash_A.find(sym_points[s]);
			if (it != cand_hash_A.end()) {
				sym_A_idx[s] = it->second;
				++candidate_count;
			} else {
				sym_A_idx[s] = -1;
			}
		} else if (!now_complete && was_complete) {
			--complete_count;
			++transversal_version_;
			if (sym_A_idx[s] >= 0) --candidate_count;
			sym_A_idx[s] = -1;
		}
	}

	// Length of the assigned prefix of A in canonical order: the count of trailing ones of canon_assigned_ (NCELLS if all assigned).
	// Kept as a bitmask rather than a running prefix length, since a retraction would force a rescan for the latter.
	size_t currentPrefix() const {
		const __uint128_t un = ~canon_assigned_;
		const uint64_t lo = (uint64_t)un;
		if (lo) return (size_t)__builtin_ctzll(lo);
		return 64 + (size_t)__builtin_ctzll((uint64_t)(un >> 64));
	}

	// Builds sigma_g from the current A. Returns false while the source line of A is not fully assigned, in which case the generator cannot be applied yet.
	bool buildRenormalization(const AOnlyGen& ag, array<int8_t, 10>& sym) const {
		sym.fill((int8_t)-1);
		for (int c = 0; c < order; ++c) {
			int v = val[ag.srcRow0[c]];
			if (v < 0) return false;
			// The ten values come from a line of a Latin square, hence are distinct; bail out rather than reject if that ever fails.
			if (sym[v] >= 0) return false;
			sym[v] = g_row0LabelA[c];
		}
		return true;
	}

	// Compares A with the renormalized image sigma_g(A o g) over the first `prefix` canonical cells.
	// Returns -1 if the image is smaller, +1 if larger, 0 if equal or an image cell is still unassigned. stopIdx is the canonical index where the scan stopped. 
	int compareRenormalized(const AOnlyGen& ag, size_t prefix, const array<int8_t, 10>& sym, int& stopIdx) const {
		const uint8_t* mapped = ag.g.mappedCell.data();
		const uint8_t* canon  = g_canonPoint.data();
		const int8_t*  v      = val.data();
		const int n = (int)prefix;
		for (int idx = 0; idx < n; ++idx) {
			const int aSrc = v[mapped[idx]];
			if (aSrc < 0) { stopIdx = idx; return 0; }
			const int aImg  = sym[aSrc];
			const int aOrig = v[canon[idx]];
			if (aImg != aOrig) { stopIdx = idx; return aImg < aOrig ? -1 : +1; }
		}
		stopIdx = n;
		return 0;
	}

	// Returns the index of the first generator proving the prefix non-minimal, or -1. Sets last_reason_points_ for a rejection.
	int findRenormalizedWitness(size_t prefix) const {
		array<int8_t, 10> sym{};

		for (size_t gi = 0; gi < g_aOnlyGens.size(); ++gi) {
			const AOnlyGen& ag = g_aOnlyGens[gi];

			if (!buildRenormalization(ag, sym)) continue;

			int stopIdx = 0;
			if (compareRenormalized(ag, prefix, sym, stopIdx) >= 0) continue;

			// The rejection depends on the compared cells, the source cells they were read from, and the line that defined sigma_g.
			__uint128_t reason = 0;
			for (int idx = 0; idx <= stopIdx && idx < NCELLS; ++idx) {
				reason |= (__uint128_t)1 << g_canonPoint[idx];
				reason |= (__uint128_t)1 << ag.g.mappedCell[idx];
			}
			for (int c = 0; c < order; ++c)
				reason |= (__uint128_t)1 << ag.srcRow0[c];
			last_reason_points_ = reason;
			return (int)gi;
		}
		return -1;
	}

	// B-feasibility of the completed transversals. Fewer than `order` survivors means no exact cover exists however the rest of A is filled in. 
	// A completed transversal that is not a candidate line can never occur in a refinement. On failure, last_reason_points_ is the union of the completed transversals.
	bool bFeasible() const {
		if (!intersects_once_BA || complete_count == 0) return true;
		if (transversal_version_ == bfeas_version_) {
			last_reason_points_ = bfeas_reason_;
			return bfeas_result_;
		}

		static thread_local vector<uint64_t> acc;
		const int words = rows_B;
		acc.assign((size_t)words, ~0ULL);
		acc[words - 1] = last_word_mask;

		__uint128_t reason = 0;
		bool ok = true;
		for (int s = 0; s < order && ok; ++s) {
			if (sym_cnt[s] != order) continue;
			reason |= sym_points[s];

			const int line = sym_A_idx[s];
			if (line < 0) {
				ok = false;
				break;
			}

			const uint64_t* row = intersects_once_BA + (long long)line * words;
			int pc = 0;
			for (int w = 0; w < words; ++w) {
				acc[w] &= row[w];
				pc += __builtin_popcountll(acc[w]);
			}
			if (pc < order) ok = false;
		}

		bfeas_version_ = transversal_version_;
		bfeas_result_ = ok;
		bfeas_reason_ = ok ? (__uint128_t)0 : reason;
		last_reason_points_ = bfeas_reason_;
		return ok;
	}

	// Appends record to dynamic_clauses_<ID>.bin for block justified by generator `gi`. Call straight after findRenormalizedWitness() returned gi, while val[] and last_reason_points_ 
	// still describe the rejection. Every false result from is_partial_solution()/operator() is followed by a clause added to the solver, so each record corresponds to one added clause.
	void logAutomorphismBlock(int gi) const {
#if WRITE_DYNAMIC_CLAUSES == 1
		if (gi < 0 || g_test_mode || !dynamic_clauses_file.is_open()) return;
		static thread_local std::string rec;
		encodeDynamicClauseRecord(rec, g_dynamic_id_bits, g_aOnlyGens[gi].autIdx, val.data(), last_reason_points_);
		if (g_dynamicDedup.seenOrInsert(dynFingerprint(rec))) {
			g_dynamic_clause_dups.fetch_add(1, std::memory_order_relaxed);
			return;
		}
		dynamic_clauses_file.write(rec.data(), (std::streamsize)rec.size());
		g_dynamic_clause_lines.fetch_add(1, std::memory_order_relaxed);
		g_dynamic_clause_bytes.fetch_add((long long)rec.size(), std::memory_order_relaxed);
#else
		(void)gi;
#endif
	}

	// Returns false (the branch is provably prunable) with last_reject_kind_/last_reason_points_ describing why.
	bool is_partial_solution(const std::vector<int>& /*pos_vars*/) const {
		DYN_TIME_SCOPE(g_a_is_partial_ns);
		bump(g_a_partial_calls);
		last_reject_kind_ = RejectKind::NONE;

		size_t prefix = currentPrefix();
		bump(g_a_prefix_sum, (long long)prefix);

		// B-feasibility first: it is cached, independent of the prefix (completed transversals need not form one), and rejects the most branches.
		{
#if TRACK_TIME == 1
			// Two clock reads per call are measurable here, so bfeas_time is only collected in TRACK_TIME builds (it reads 0 otherwise).
			auto t0 = chrono::steady_clock::now();
#endif
			bool feasible = bFeasible();
#if TRACK_TIME == 1
			bump(g_a_bfeas_ns, chrono::duration_cast<chrono::nanoseconds>(chrono::steady_clock::now() - t0).count());
#endif
			if (!feasible) {
				last_reject_kind_ = RejectKind::B_INFEASIBLE;
				bump(g_a_partial_rejects);
				bump(g_a_bfeas_rejects);
				return false;
			}
		}

		if (prefix == 0) return true;

		const int witness = findRenormalizedWitness(prefix);
		if (witness >= 0) {
			last_reject_kind_ = RejectKind::SYMMETRY;
			logAutomorphismBlock(witness);
			bump(g_a_partial_rejects);
			bump(g_a_symmetry_rejects);
			return false;
		}
		return true;
	}

	bool should_early() const { return true; }

	// Keep only the literals of the reason cells; the shorter clause is implied by the same fact and prunes more.
	void minimize(std::vector<int>& clause) const {
		DYN_TIME_SCOPE(g_a_minimize_ns);
		if (last_reject_kind_ == RejectKind::NONE) return;
		const __uint128_t reason = last_reason_points_;
		if (reason == 0) return;

		static thread_local std::vector<int> keep;   // reused so the rewrite does not allocate
		keep.clear();
		keep.reserve(clause.size());
		for (int lit : clause) {
			const int v = lit < 0 ? -lit : lit;
			if ((unsigned)(v - 1) >= (unsigned)(order * order * order)) { keep.push_back(lit); continue; }   // not an A variable
			if (((reason >> g_varPoint[v]) & 1) != 0) keep.push_back(lit);
		}
		if (!keep.empty() && keep.size() < clause.size()) {
			g_a_clause_lits_before.fetch_add((long long)clause.size(), std::memory_order_relaxed);
			g_a_clause_lits_after.fetch_add((long long)keep.size(), std::memory_order_relaxed);
			g_a_clauses_minimized.fetch_add(1, std::memory_order_relaxed);
			clause.swap(keep);
		}
	}

	bool operator()(const std::vector<int>& solution) const {
		DYN_TIME_SCOPE(g_a_operator_ns);
		(void)solution;

		// Reached only once every observed A variable is assigned.
		if (complete_count != order) return true;

		g_a_full_models.fetch_add(1, std::memory_order_relaxed);

		// Authoritative minimality check on the full grid, in case is_partial_solution() missed it.
		const int fullWitness = findRenormalizedWitness(NCELLS);
		if (fullWitness >= 0) {
			logAutomorphismBlock(fullWitness);
			// No B can rescue a non-minimal A, so skip the refinement and just block it.
			g_a_full_rejects.fetch_add(1, std::memory_order_relaxed);
			return false;
		}

		++g_raw_solutions_seen;
		g_a_sent_to_refinement.fetch_add(1, std::memory_order_relaxed);

		// A refinement needs all ten A transversals to be candidate lines and at least `order` surviving B lines (cached by is_partial_solution()).
		if (candidate_count == order && bFeasible())
			(void)solve_partial_solution(sym_A_idx);

		if (g_raw_solutions_seen % 50000 == 0)
			cout << "[A " << g_raw_solutions_seen << "] "
				 << "refinements=" << total_refinements
				 << " (partial_count=" << partial_count << ")"
				 << " partial_calls=" << g_a_partial_calls.load(std::memory_order_relaxed)
				 << " partial_rejects=" << g_a_partial_rejects.load(std::memory_order_relaxed)
				 << " full_rejects=" << g_a_full_rejects.load(std::memory_order_relaxed)
				 << " sent_to_refinement=" << g_a_sent_to_refinement.load(std::memory_order_relaxed)
				 << "\n";

		return false;
	}

	explicit operator bool() const { return true; }

	static constexpr bool notifyAssignment = true;
	static constexpr bool earlyClause = true;
	static constexpr bool minimizeClause = true;
};

// -----------------------------------------------------------------------------
// Cube-and-conquer (optional; enabled by --r)
//
// march_cu splits the CNF into disjoint cubes (partial assignments of A's variables) and each cube is solved on its own copy of the base solver. 
// march_cu is restricted with -m Q_MAX_VAR to branch only on variables 1..Q_MAX_VAR, which by var()'s layout are exactly A's, so the cubes partition the assignments of A 
// and no two cubes can find the same A. Solving every cube and summing gives the same result as one solve.
//
// tuneRParameter() picks march_cu's -r (number of free A variables removed before a cube is emitted; smaller r = fewer, harder cubes). 
// It generates cubes, solves a few of them under a timeout, and from the average time estimates the total. It raises r until the average cube time reaches
// R_TEST_TARGET_SECONDS, or estimate stops improving (then it reverts to the previous r).
// -----------------------------------------------------------------------------

// A occupies variables 1..Q_MAX_VAR; passed to march_cu's -m so it only branches on A.
constexpr int Q_MAX_VAR = order * order * order;

static string g_march_cu_path = default_march_cu_path;   // --march-cu

// > 0: march_cu -r value; tuneRParameter() starts from it. It is stored negated once tuning has settled. <= 0: skip march_cu and reuse the cubes file already on disk (see generateCubes()). 
// Only used when --r is given.
static int CUBE_R_PARAM = 50;
static int CUBE_LIMIT   = 0;   // march_cu -l: cap on the number of cubes; 0 keeps march_cu's default
static int CUBE_START   = 0;   // first cube to solve (inclusive), to split a run across invocations
static int CUBE_END     = 0;   // last cube to solve (exclusive); <= 0 means through the last cube
static string JOB_ID    = "";  // keeps output filenames apart for concurrent runs

static double total_cube_creation_time = 0.0;   // solver copy + cube literals, real cubes only
static double total_cube_solve_time    = 0.0;   // CaDiCaL solve time, real cubes only
static double total_cube_gen_time      = 0.0;   // last march_cu invocation
static double total_cube_tune_time     = 0.0;   // all of tuneRParameter()
static int    cube_count = 0;                   // cubes returned by the last generateCubes()

static const int R_CUBES_TESTED = 5;                                                  // cubes sampled per tuning round, besides cube 0
static const double R_TEST_TARGET_SECONDS  = 90.0;                                    // desired average time per real cube
static const double R_TEST_TIMEOUT_SECONDS = R_TEST_TARGET_SECONDS * R_CUBES_TESTED;  // per-probe timeout
static const int R_INCREASE = 10;                                                     // growth of r between rounds

// Parses a march_cu .icnf file: each cube is a line "a <literals> 0".
static vector<vector<int>> parseCubesFile(const string& path) {
	vector<vector<int>> cubes;
	ifstream f(path);
	if (!f.is_open()) {
		cerr << "[cubing] Cannot open cubes file: " << path << "\n";
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
		cubes.push_back(std::move(cube));
	}
	return cubes;
}

// Dumps the formula to DIMACS, runs march_cu on it (-r CUBE_R_PARAM, -m Q_MAX_VAR, optionally -l CUBE_LIMIT) and parses the cubes. If
// CUBE_R_PARAM <= 0, march_cu is skipped and the cubes file from an earlier run is parsed as is.
static vector<vector<int>> generateCubes(CaDiCaL::Solver& base_solver, const string& parent_dir) {
	auto t0 = chrono::steady_clock::now();

	string cnf_path   = parent_dir + "/encoding_" + to_string(TEMPLATE_ID) + ".cnf";
	string cubes_path = parent_dir + "/cubes_" + to_string(TEMPLATE_ID) + ".icnf";

	if (CUBE_R_PARAM > 0) {
		{
			cerr << "[cubing] Writing CNF to: " << cnf_path << "\n";
			CaDiCaL::Solver dumper;
			base_solver.copy(dumper);
			int stdout_save = dup(fileno(stdout));
			freopen(cnf_path.c_str(), "w", stdout);
			dumper.dump_cnf();
			fflush(stdout);
			dup2(stdout_save, fileno(stdout));
			close(stdout_save);
		}

		ostringstream cmd;
		cmd << g_march_cu_path << " " << cnf_path << " -r " << CUBE_R_PARAM << " -m " << Q_MAX_VAR;
		if (CUBE_LIMIT > 0)
			cmd << " -l " << CUBE_LIMIT;
		cmd << " -o " << cubes_path;

		cerr << "[cubing] Running: " << cmd.str() << "\n";
		int ret = system(cmd.str().c_str());
		double elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
		if (ret != 0) {
			cerr << "[cubing] march_cu failed with exit code " << ret << "\n";
			return {};
		}
		cerr << "[cubing] Cubing time: " << elapsed << "s\n";
		total_cube_gen_time = elapsed;
	}

	auto cubes = parseCubesFile(cubes_path);
	cerr << "[cubing] Cubes generated: " << cubes.size() << "\n";
	cube_count = (int)cubes.size();
	return cubes;
}

// Lets CaDiCaL unwind solve() once a tuning probe has exceeded its time limit.
struct CubeTimeoutTerminator : public CaDiCaL::Terminator {
	chrono::steady_clock::time_point start;
	double limit_seconds;
	bool   hit = false;

	explicit CubeTimeoutTerminator(double limit_seconds_) : start(chrono::steady_clock::now()), limit_seconds(limit_seconds_) {}

	bool terminate() override {
		if (g_stop_requested) return true; // not a timeout, so `hit` stays false
		double elapsed = chrono::duration<double>(chrono::steady_clock::now() - start).count();
		if (elapsed > limit_seconds) {
			hit = true;
			return true;
		}
		return false;
	}
};

// Solves one cube under a timeout, only to measure its time (see the block comment above). Returns true on timeout.
template <typename Policy>
static bool testSolveCube(CaDiCaL::Solver& base_solver, const ExhaustiveSearchOptions& opts, const vector<int>& cube, double& elapsed_out) {
	CaDiCaL::Solver copy;
	base_solver.copy(copy);
	for (int lit : cube)
		copy.clause(lit);

	ExhaustiveSearch<Policy> propagator(&copy, opts, Policy());

	CubeTimeoutTerminator term(R_TEST_TIMEOUT_SECONDS);
	copy.connect_terminator(&term);

	g_test_mode = true;
	auto t_start = chrono::steady_clock::now();

	copy.solve(); // returns UNKNOWN if the terminator fired

	g_test_mode = false;
	elapsed_out = chrono::duration<double>(chrono::steady_clock::now() - t_start).count();

	copy.disconnect_terminator();
	return term.hit;
}

// Cube 0 plus R_CUBES_TESTED cubes spread roughly evenly over the rest, so the timing estimate does not depend on the cubes that sort first.
static vector<int> pickSampleCubeIndices(int cube_amount) {
	vector<int> idxs;
	if (cube_amount <= 0) return idxs;

	if (cube_amount <= R_CUBES_TESTED) {
		for (int i = 0; i < cube_amount; ++i)
			idxs.push_back(i);
		return idxs;
	}

	idxs.push_back(0);

	for (int i = 0; i < R_CUBES_TESTED; ++i) {
		int start = max((i * cube_amount) / R_CUBES_TESTED, 1);
		int end   = ((i + 1) * cube_amount) / R_CUBES_TESTED;

		int idx = start + rand() % max(1, end - start);
		idxs.push_back(idx);
	}

	return idxs;
}

// Searches for an r that keeps the average cube time near R_TEST_TARGET_SECONDS (see the block comment above). Leaves CUBE_R_PARAM negated and returns the cubes for the chosen r.
template <typename Policy>
static vector<vector<int>> tuneRParameter(CaDiCaL::Solver& base_solver, const ExhaustiveSearchOptions& opts, const string& parent_dir) {
	auto t0 = chrono::steady_clock::now();
	vector<vector<int>> cubes;

	int prev_r = -1;   // best r so far, -1 if none yet
	double prev_estimate = -1.0;
	vector<vector<int>> prev_cubes;

	cerr << "[r-tuning] START:\n";

	while (true) {
		cerr << "\n[r-tuning] Generating cubes with r=" << CUBE_R_PARAM << " to test timing...\n";
		cubes = generateCubes(base_solver, parent_dir);
		if (cubes.empty()) {
			cerr << "[r-tuning] No cubes generated; aborting r-tuning.\n";
			break;
		}

		vector<int> sample = pickSampleCubeIndices((int)cubes.size());

		bool any_timeout = false;
		double total_time = 0.0;
		int tested = 0;

		for (int idx : sample) {
			double elapsed = 0.0;
			bool timed_out = testSolveCube<Policy>(base_solver, opts, cubes[idx], elapsed);
			cerr << "[r-tuning] Test cube " << idx << "/" << cubes.size() << ": " << (timed_out ? "TIMEOUT" : "solved") << " in " << elapsed << "s\n";
			cerr.flush();

			if (g_stop_requested) break;

			if (timed_out) {
				any_timeout = true;
				break;
			}
			total_time += elapsed;
			++tested;
		}

		if (g_stop_requested) {
			cerr << "[r-tuning] Stop requested; aborting r-tuning.\n";
			break;
		}

		if (any_timeout) {
			CUBE_R_PARAM = CUBE_R_PARAM + R_INCREASE;
			cerr << "[r-tuning] r_parameter: " << CUBE_R_PARAM << "\n";
			continue;
		}

		double avg = tested > 0 ? total_time / tested : 0.0;
		double estimate = cubes.size() * avg;
		cerr << "[r-tuning] Average test cube time: " << avg << "s over " << tested << " cube(s)\n";
		cerr << "[r-tuning] Estimated total solve time at r=" << CUBE_R_PARAM << ": " << estimate
			 << "s (" << cubes.size() << " cubes * " << avg << "s avg)\n";

		if (avg <= R_TEST_TARGET_SECONDS) {
			cerr << "[r-tuning] Average test cube time below target: " << R_TEST_TARGET_SECONDS << "s, ending early\n";
			CUBE_R_PARAM = -CUBE_R_PARAM;
			cerr << "[r-tuning] r_parameter: " << CUBE_R_PARAM << "\n";
			break;
		}

		if (prev_estimate >= 0.0 && estimate > prev_estimate) {
			cerr << "[r-tuning] Estimated time increased (" << estimate << "s > " << prev_estimate
				 << "s at r=" << prev_r << "); reverting to r=" << prev_r << " and continuing.\n";
			CUBE_R_PARAM = -prev_r;
			cubes = std::move(prev_cubes);
			cerr << "[r-tuning] r_parameter: " << CUBE_R_PARAM << "\n";
			break;
		}

		prev_r = CUBE_R_PARAM;
		prev_estimate = estimate;
		prev_cubes = cubes;

		CUBE_R_PARAM = CUBE_R_PARAM + R_INCREASE;
		cerr << "[r-tuning] r_parameter: " << CUBE_R_PARAM << "\n";
	}

	cerr << "[r-tuning] DONE, rolling back probe-solve side effects.\n";

	// processLine() counts partial_count even in test mode, so it must be reset; the other two are reset for robustness.
	partial_count = 0;
	total_refinements = 0;
	skipped_partial_solutions = 0;

	total_cube_tune_time = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	return cubes;
}

// Solves one real cube on a copy of the base solver, with a fresh policy, like the non-cubed path in main(). Returns the number of complete A squares found in it.
template <typename Policy>
static long long solveOneCube(CaDiCaL::Solver& base_solver, const ExhaustiveSearchOptions& opts, const vector<int>& cube, int cube_index) {
	auto t0 = chrono::steady_clock::now();
	const long refinements_before = total_refinements;

#if WRITE_PROOFS == 2
	ProofSizeTracer proof_size_tracer; // declared before `copy` so it outlives the solver
#endif

	CaDiCaL::Solver copy;

#if WRITE_PROOFS == 2
	// Connect while the solver is still unconfigured, before the cube's unit clauses are added, so every lemma of the solve is counted.
	copy.connect_proof_tracer(&proof_size_tracer, false);
#endif

#if WRITE_PROOFS == 1
	// Trace the DRAT proof before the cube's unit clauses are added, so the whole solve is covered.
	long long proof_length_field_pos = -1, proof_start_pos = -1;
	if (g_proof_blob_fp)
		proof_length_field_pos = begin_cube_proof_record(copy, (uint32_t)cube_index, proof_start_pos);
#endif

	base_solver.copy(copy);

	for (int lit : cube)
		copy.clause(lit);

	copy.connect_terminator(&g_signal_terminator);

	ExhaustiveSearch<Policy> propagator(&copy, opts, Policy());

	double create_elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	total_cube_creation_time += create_elapsed;

	t0 = chrono::steady_clock::now();
	copy.solve();
	copy.disconnect_terminator();
	double solve_elapsed = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	total_cube_solve_time += solve_elapsed;

#if WRITE_PROOFS == 1
	if (g_proof_blob_fp)
		end_cube_proof_record(copy, proof_length_field_pos, proof_start_pos);
#endif

 	long long count = propagator.get_solution_count();

#if WRITE_PROOFS == 2
 	cerr << "[cubing] Cube " << cube_index << " (" << cube.size() << " lits): " << count
 		 << " complete A squares, took " << solve_elapsed << "/" << total_cube_solve_time
		 << "s solve (" << create_elapsed << "/" << total_cube_creation_time << "s create), " 
		 << (total_refinements - refinements_before) << " refinements, proof size: " << proof_size_tracer.bytes() << " bytes\n";
	std::cout.flush();
	copy.disconnect_proof_tracer(&proof_size_tracer);
	std::fflush(stdout);
#else
 	cerr << "[cubing] Cube " << cube_index << " (" << cube.size() << " lits): " << count
 		 << " complete A squares, took " << solve_elapsed << "/" << total_cube_solve_time
		 << "s solve (" << create_elapsed << "/" << total_cube_creation_time << "s create), " << (total_refinements - refinements_before) << " refinements\n";
#endif
	return count;
}

// Tunes r (or reuses cubes if CUBE_R_PARAM <= 0), then solves cubes [CUBE_START, CUBE_END) in sequence. Returns the total number of complete A squares found, comparable to the non-cubed path's count.
template <typename Policy>
static long long runCubedSearch(CaDiCaL::Solver& base_solver, const ExhaustiveSearchOptions& opts, const string& parent_dir) {
	int display_r = CUBE_R_PARAM < 0 ? -CUBE_R_PARAM : CUBE_R_PARAM;
	cerr << "[cubing] Generating cubes via march_cu (path=" << g_march_cu_path
		 << ", -r=" << display_r << ", -m=" << Q_MAX_VAR << " [A vars only]";
	if (CUBE_LIMIT > 0) cerr << ", -l=" << CUBE_LIMIT;
	cerr << ")\n";

	vector<vector<int>> cubes = (CUBE_R_PARAM > 0) ? tuneRParameter<Policy>(base_solver, opts, parent_dir) : generateCubes(base_solver, parent_dir);

	if (cubes.empty()) {
		cerr << "[cubing] No cubes generated (formula UNSAT during cubing, or march_cu error).\n";
		return 0;
	}

	int cube_amount = (int)cubes.size();
	int cube_start = max(0, CUBE_START);
	int cube_end   = (CUBE_END > 0) ? min(CUBE_END, cube_amount) : cube_amount;

	int interval = max(1, min(2000, (cube_end - cube_start) / 10));
	auto wall_start = chrono::steady_clock::now();

	long long raw_solution_count = 0;
	cerr << "[cubing] Solving cubes " << cube_start << ".." << (cube_end - 1) << " of " << cubes.size() << " total:\n";
	for (int i = cube_start; i < cube_end; ++i) {
		raw_solution_count += solveOneCube<Policy>(base_solver, opts, cubes[i], i);

		// Checked only after solveOneCube() and its records have fully finished: no new cube starts after a stop request, and the cube in flight is never cut off.
		if (g_stop_requested) {
			cerr << "[cubing] Stop requested (signal " << (int)g_stop_signal << ") after cube " << i << "/" << (cube_end - 1) << "; finishing up, no further cubes will be started.\n";
			cerr.flush();
			flush_output();
			break;
		}

		if ((i - cube_start) % interval == 0) {
			long long done = i - cube_start + 1;
			double avg_solve  = total_cube_solve_time / (double)done;
			double avg_create = total_cube_creation_time / (double)done;
			cerr << "[cubing] " << (i + 1) << "/" << cubes.size() << ": average solve=" << avg_solve << "s, average create=" << avg_create
				 << "s, ETA=" << (cube_end - cube_start - done) * (avg_solve + avg_create) << "s\n";
			cerr.flush();
		}
	}

	double total_elapsed = chrono::duration<double>(chrono::steady_clock::now() - wall_start).count();
	cerr << "[cubing] Cube-solving wall time: " << total_elapsed << "s, " << raw_solution_count << " complete A squares\n";
	return raw_solution_count;
}

// -----------------------------------------------------------------------------
// Program entry point
// -----------------------------------------------------------------------------
int main(int argc, char* argv[]) {
	install_stop_handler(); // SIGINT/SIGTERM only set a flag; see partial_solution_refinement.cpp

	if (argc < 2) {
		cerr << "Usage: " << argv[0] << " <template.txt | TEMPLATE_ID> [--bin <templates.bin>] [--set name=value ...]\n";
		cerr << "       [--r <r_param>] [--cube-start <i>] [--cube-end <j>] [--cube-limit <n>] [--job-id <id>] [--march-cu <path>]\n";
		cerr << "       A numeric first argument selects that record of the packed binary template file\n";
		cerr << "       (default " << default_binary_file << "); anything else is read as a text template.\n";
		cerr << "       --r enables march_cu cube splitting: a positive value starts adaptive r-parameter tuning from that r;\n";
		cerr << "       zero or negative reuses an already-generated cubes file. Without --r the whole formula is solved in one pass.\n";
		return 1;
	}

	string template_arg  = argv[1];
	string binary_file   = default_binary_file;
	bool cubing_enabled  = false;
	vector<pair<string, int>> solver_overrides;
	for (int i = 2; i < argc; ++i) {
		const string arg = argv[i];
		auto value = [&]() -> const char* {
			if (i + 1 >= argc) {
				cerr << "Missing value for " << arg << "\n";
				return nullptr;
			}
			return argv[++i];
		};

		const char* v = nullptr;
		if (arg == "--bin") {
			if (!(v = value())) return 1;
			binary_file = v;
		} else if (arg == "--r") {
			if (!(v = value())) return 1;
			CUBE_R_PARAM = atoi(v);
			cubing_enabled = true;
		} else if (arg == "--cube-start") {
			if (!(v = value())) return 1;
			CUBE_START = atoi(v);
		} else if (arg == "--cube-end") {
			if (!(v = value())) return 1;
			CUBE_END = atoi(v);
		} else if (arg == "--cube-limit") {
			if (!(v = value())) return 1;
			CUBE_LIMIT = atoi(v);
		} else if (arg == "--job-id") {
			if (!(v = value())) return 1;
			JOB_ID = v;
		} else if (arg == "--march-cu") {
			if (!(v = value())) return 1;
			g_march_cu_path = v;
		} else if (arg == "--set") {
			if (!(v = value())) return 1;
			string kv = v;
			size_t eq = kv.find('=');
			if (eq == string::npos) {
				cerr << "Bad --set argument (expected name=value): " << kv << "\n";
				return 1;
			}
			solver_overrides.push_back({kv.substr(0, eq), atoi(kv.substr(eq + 1).c_str())});
		} else {
			cerr << "Unrecognized argument: " << arg << "\n";
			return 1;
		}
	}

	// An all-digit first argument is a record index into templates.bin; anything else is the path of a text template.
	const bool from_binary = !template_arg.empty() && template_arg.find_first_not_of("0123456789") == string::npos;

	string template_path; // empty when the template did not come from a text file
	string template_source;
	if (from_binary) {
		TEMPLATE_ID = atoi(template_arg.c_str());
		template_source = binary_file + "#" + to_string(TEMPLATE_ID);
		cerr << "[setup] Loading template " << TEMPLATE_ID << " from " << binary_file << "\n";
		if (!readTemplateBinary(binary_file, TEMPLATE_ID)) return 1;
	} else {
		template_path = template_arg;
		template_source = template_path;
		if (!readTemplateFile(template_path)) return 1;
	}

	loadTemplateAutomorphisms(template_path, binary_file, TEMPLATE_ID);
	cout << "order=" << order << "\n";
	cout << "template=" << template_source << "\n";
	if (from_binary)
		cout << "template_id=" << TEMPLATE_ID << "\n";
	cout << "refinement engine=" << (SATREFINEMENT ? "SAT exact cover" : "custom exact cover") << "\n";
	cout << "proof engine = " << (WRITE_PROOFS == 0 ? "no proofs" : (WRITE_PROOFS == 1 ? "DRAT proof per cube" : "internal LRAT proof check and DRAT proof size per cube")) << "\n";
	cout << "relation type=4^4 (4444)\n"; 
	cout << "cubing: " << (cubing_enabled ? "ON" : "OFF") << "\n";
	if (cubing_enabled) {
		cout << "  r_parameter: " << CUBE_R_PARAM << "\n";
		cout << "  cube_start: " << CUBE_START << "\n";
		cout << "  cube_end: " << (CUBE_END > 0 ? to_string(CUBE_END) : string("(all)")) << "\n";
		if (CUBE_LIMIT > 0) cout << "  cube_limit: " << CUBE_LIMIT << "\n";
		if (!JOB_ID.empty()) cout << "  job_id: " << JOB_ID << "\n";
		cout << "  march_cu: " << g_march_cu_path << "\n";
	}

	buildCanonicalOrder();
	setupAOnlyGenerators();
	setupPairGenerators();
	g_pair_filter = &pairLevelAccept;

	CaDiCaL::Solver solver;
	solver.set("binary", 1);
	solver.set("report", 0);
	solver.set("inprocessing", 0);
	solver.set("factorcheck", 0);
	solver.set("factor", 0);
#if WRITE_PROOFS == 2
	// Internal LRAT checking
	solver.set("check", 1);
	solver.set("checkproof", 2);
#endif
	for (auto& [name, value] : solver_overrides) {
		bool ok = solver.set(name.c_str(), value);
		cerr << "solver.set(\"" << name << "\", " << value << ") -> " << (ok ? "ok" : "REJECTED (bad name or out of range)") << "\n";
		if (!ok) return 1;
	}

	cerr << "[setup] Building CNF...\n";
	cerr.flush();
	auto ts1 = chrono::steady_clock::now();
	buildFormula(solver);
	cerr << "[setup] CNF complete in " << chrono::duration<double>(chrono::steady_clock::now() - ts1).count() << "s\n";

	// Candidate lines and intersection tables for the refinement engine.
	vector<vector<vector<int>>> refinementTemplate(2, vector<vector<int>>(order, vector<int>(order, 0)));
	for (int sq = 0; sq < 2; ++sq)
		for (int r = 0; r < order; ++r)
			for (int c = 0; c < order; ++c)
				refinementTemplate[sq][r][c] = TEMPLATE_F[sq][r][c];

	cerr << "[setup] Prebuilding refinement candidate structures...\n";
	cerr.flush();
	string refinement_id = (from_binary ? ("template_dynamic_" + to_string(TEMPLATE_ID)) : "template_dynamic") + "_" + JOB_ID;
	string output_dir = makeOutputDir(from_binary, TEMPLATE_ID, template_path);
	cerr << "[setup] Output directory: " << output_dir << "\n";
	if (setup(refinementTemplate, output_dir, refinement_id) != 0) {
		cerr << "FATAL: refinement setup failed.\n";
		return 1;
	}
	writeDynamicClausesHeader();
	cerr << "[setup] Dynamic clauses log: " << dynamic_clauses_path << "\n";
	cerr << "[setup] Refinement candidate structures ready: A-lines=" << count_A << ", B-lines=" << count_B << "\n";
	cerr << "[search] Entering exhaustive SAT search...\n";
	cerr.flush();

	auto t0 = chrono::steady_clock::now();
	long long raw_solution_count = 0;

	// Observe A only, in canonical cell order.
	vector<int> observed;
	observed.reserve(order * order * order);
	for (int idx = 0; idx < NCELLS; ++idx) {
		auto [r, c] = canonicalCells[idx];
		for (int s = 0; s < order; ++s)
			observed.push_back(var(0, r, c, s));
	}

	ExhaustiveSearchOptions opts;
	opts.to_observe = observed;
	opts.only_neg = true;
	opts.can_forget = true;

	for (int v : observed)
		solver.freeze(v);

	if (cubing_enabled) {
		raw_solution_count = runCubedSearch<DynamicAOnlyPolicy>(solver, opts, output_path);
	} else {
		ExhaustiveSearch<DynamicAOnlyPolicy> propagator(&solver, opts, DynamicAOnlyPolicy());

		solver.connect_terminator(&g_signal_terminator);

		g_search_running.store(true, std::memory_order_relaxed);
		std::thread heartbeat(searchHeartbeat, 30.0);
		auto solve_t0 = chrono::steady_clock::now();

		solver.solve();
		solver.disconnect_terminator();

		double solve_elapsed = chrono::duration<double>(chrono::steady_clock::now() - solve_t0).count();

		g_search_running.store(false, std::memory_order_relaxed);
		heartbeat.join();

		cerr << "[search] solver.solve() returned after " << solve_elapsed << "s\n";
		raw_solution_count = propagator.get_solution_count();
	}

	cout << "\n===== A/refinement enumeration =====\n";
	if (g_stop_requested)
		cout << "*** RUN INTERRUPTED (signal " << (int)g_stop_signal << ") -- results below are partial/incomplete ***\n";
	cout << "Complete A squares enumerated: " << raw_solution_count << "\n";
	cout << "Refinements found: " << total_refinements << "\n";
	cout << "Partial A candidates processed: " << partial_count << "\n";
	cout << "A candidates with no refinement: " << skipped_partial_solutions << "\n";
	cout << "\n----- A-only dynamic pruning stats -----\n";
	cout << "is_partial_solution calls: " << g_a_partial_calls.load(std::memory_order_relaxed) << "\n";
	cout << "Partial A branches rejected early: " << g_a_partial_rejects.load(std::memory_order_relaxed) << "\n";
	cout << "Complete A models seen: " << g_a_full_models.load(std::memory_order_relaxed) << "\n";
	cout << "Complete A rejected at full-grid check (missed by partial pruning): " << g_a_full_rejects.load(std::memory_order_relaxed) << "\n";
	cout << "Complete A sent to refinement engine: " << g_a_sent_to_refinement.load(std::memory_order_relaxed) << "\n";
	cout << "Dynamic clause records logged: " << g_dynamic_clause_lines.load(std::memory_order_relaxed) << " (" << g_dynamic_clause_bytes.load(std::memory_order_relaxed) << " bytes incl. header, " << dynamic_clauses_path << ")\n";
	cout << "Dynamic clause repeats skipped: " << g_dynamic_clause_dups.load(std::memory_order_relaxed)
		 << " (dedup table " << (g_dynamicDedup.bytes() >> 10) << " KiB for " << g_dynamicDedup.used << " records, cap " << DYNAMIC_DEDUP_MAX_MB << " MiB"
		 << (g_dynamicDedup.full ? ", CAP REACHED: later repeats are written again" : "") << ")\n";
	long long partial_calls = g_a_partial_calls.load(std::memory_order_relaxed);
	if (partial_calls > 0) {
		cout << "Partial reject rate: " << (100.0 * g_a_partial_rejects.load(std::memory_order_relaxed) / partial_calls) << "%\n";
		cout << "Mean known prefix at call: " << ((double)g_a_prefix_sum.load(std::memory_order_relaxed) / partial_calls) << " / " << NCELLS << " cells\n";
	}
	long long full_models = g_a_full_models.load(std::memory_order_relaxed);
	if (full_models > 0)
		cout << "Complete-A symmetry block rate: " << (100.0 * g_a_full_rejects.load(std::memory_order_relaxed) / full_models) << "%\n";
	printRejectionSummary(cout);

	cout << "\n----- Refinement timings -----\n";
	cout << "Total wall time (incl. setup): " << chrono::duration<double>(chrono::steady_clock::now() - start_time).count() << "s\n";
	cout << "Search-step elapsed: " << chrono::duration<double>(chrono::steady_clock::now() - t0).count() << "s\n";
#if TRACK_TIME == 1
	cout << "Refinement candidate discovery time: " << candidate_find_time << "s\n";
	cout << "Refinement precompute time: " << precompute_time << "s\n";
	cout << "Refinement line-intersection time: " << total_line_intersection_time << "s\n";
	cout << "Refinement exact-cover solve time: " << total_refinement_solve_time << "s\n";
	cout << "Refinement early-blocking time: " << total_refinement_early_blocking << "s\n";
	cout << "Refinement total time: " << candidate_find_time + precompute_time + total_line_intersection_time + total_refinement_solve_time + total_refinement_early_blocking << "s\n";
#endif

#if TRACK_TIME == 1
	{
		double is_partial_s = g_a_is_partial_ns.load(std::memory_order_relaxed) / 1e9;
		double minimize_s   = g_a_minimize_ns.load(std::memory_order_relaxed) / 1e9;
		double operator_s   = g_a_operator_ns.load(std::memory_order_relaxed) / 1e9;

		cout << "\n----- Dynamic policy timings -----\n";
		cout << "is_partial_solution() total time: " << is_partial_s << "s\n";
		cout << "  of which B-feasibility check: " << (g_a_bfeas_ns.load(std::memory_order_relaxed) / 1e9) << "s\n";
		cout << "minimize() total time: " << minimize_s << "s\n";
		cout << "operator() total time (full-grid check + refinement handoff): " << operator_s << "s\n";
		cout << "Dynamic policy total (excl. notify_assignment and refinement): " << is_partial_s + minimize_s + operator_s << "s\n";
	}
#endif

	if (cubing_enabled) {
		cout << "\n----- Cubing -----\n";
		cout << "Cubes generated: " << cube_count << "\n";
		int final_r = CUBE_R_PARAM < 0 ? -CUBE_R_PARAM : CUBE_R_PARAM;
		cout << "Final r_parameter: " << final_r << "\n";
		if (total_cube_tune_time > 0.0)
			cout << "r-tuning time: " << total_cube_tune_time << "s (includes cube generation and probe solves during tuning)\n";
		cout << "Cube generation time (march_cu, last invocation): " << total_cube_gen_time << "s\n";
		cout << "Cube solver-copy/creation time (real cubes only): " << total_cube_creation_time << "s\n";
		cout << "Cube solve time (real cubes only): " << total_cube_solve_time << "s\n";
	}

	std::fflush(stdout);
	std::fflush(stderr);
	std::cout.flush();
	std::cerr.flush();
	flush_output();
	outfile.close();
	close_dynamic_clauses();
	close_proof_blob();

	// 128 + signal if the run was cut short by SIGINT/SIGTERM, so wrapper scripts can tell an incomplete template from a clean one via $?.
	return stop_exit_code();
}