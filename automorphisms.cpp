// template_automorphisms.cpp
//
// Computes Aut(T) from template T (from Gill & Wanless, "Pairs of MOLS of order ten satisfying non-trivial relations" (2022), Section 3)
//
// A template of order n=10 and type (lambda0,lambda1,lambda2,lambda3) consists of:
//   - a set of "relational" rows, by convention rows 0..lambda0-1
//   - a set of "relational" columns, by convention columns 0..lambda1-1
//   - two binary frequency squares F0, F1 (10x10 arrays of 0/1), where Ft has frequency (10-lambda_{t+2}) zeros and lambda_{t+2} ones in every row and every column.
//
// Two templates of the same type are isomorphic (paper, Section 3) if one can be obtained from the other by:
//   1. permuting rows, mapping relational rows to relational rows,
//   2. permuting columns, mapping relational columns to relational columns,
//   3. transposing everything (rows <-> columns),
//   4. reordering (i.e. swapping) the two frequency squares.
// Aut(T) is the group of such operations that map T to itself.
//
// This file builds a colored graph whose automorphism group is exactly Aut(T) as defined above, runs nauty on it, and decodes every reported generator into: 
// 		a row permutation, a column permutation, whether rows/columns were transposed, and whether F0/F1 were swapped.
//
// The template can be given either way:
//
//   * a text file: 10 lines of 10 characters ('0'/'1') for F0, then (optionally blank line(s),) 10 lines of 10 characters for F1
//
//   * a record index into the packed binary template file (a first argument made only of digits)
//
// lambda_row / lambda_col default to 4 (type 4^4, the common case in the paper); override them if your template has a different row/column relational count. 

#include <array>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <cstring>
#include <cstdint>
#include <cstdlib>
#include <unordered_set>

#include "nauty.h"
#include "nausparse.h"

using namespace std;

// -----------------------------------------------------------------------
// Vertex layout
// -----------------------------------------------------------------------
constexpr int ROW_HUB = 0;
constexpr int COL_HUB = 1;
constexpr int F0_HUB  = 2;
constexpr int F1_HUB  = 3;

constexpr int ROW_BASE = 4;              // rows:      4 .. 13
constexpr int COL_BASE = ROW_BASE + 10;  // cols:     14 .. 23
constexpr int F0_BASE  = COL_BASE + 10;  // F0 syms:  24 .. 25  (value 0, value 1)
constexpr int F1_BASE  = F0_BASE + 2;    // F1 syms:  26 .. 27  (value 0, value 1)
constexpr int CELL_BASE = F1_BASE + 2;   // cells:    28 .. 127

constexpr int N_NAUTY = CELL_BASE + 100; // = 128

static inline int cell_vertex(int i, int j) { return CELL_BASE + i * 10 + j; }

// -----------------------------------------------------------------------
// Reading the template file
// -----------------------------------------------------------------------
static bool read_bits_block(ifstream& in, int arr[10][10]) {
	int row = 0;
	string line;
	while (row < 10 && getline(in, line)) {
		// strip whitespace/CR
		string s;
		for (char c : line) if (c == '0' || c == '1') s.push_back(c);
		if (s.empty()) continue; // skip blank lines
		if ((int)s.size() != 10) {
			cerr << "Malformed line (expected 10 bits, got " << s.size() << "): " << line << "\n";
			return false;
		}
		for (int j = 0; j < 10; ++j) arr[row][j] = s[j] - '0';
		++row;
	}
	return row == 10;
}

static bool read_template(const string& path, int F0[10][10], int F1[10][10]) {
	ifstream in(path);
	if (!in) { cerr << "Cannot open template file: " << path << "\n"; return false; }
	if (!read_bits_block(in, F0)) { cerr << "Failed to read F0 block (need 10 lines of 10 bits)\n"; return false; }
	if (!read_bits_block(in, F1)) { cerr << "Failed to read F1 block (need 10 lines of 10 bits)\n"; return false; }
	return true;
}

// Default location of the packed binary template file when none is given on the command line
#ifndef DEFAULT_TEMPLATE_BIN
#define DEFAULT_TEMPLATE_BIN "templates.bin"
#endif

// -----------------------------------------------------------------------
// Reading the template from the packed binary file
// -----------------------------------------------------------------------
static bool read_template_binary(const string& binary_path, int template_id, int F0[10][10], int F1[10][10]) {
	if (template_id < 0) {
		cerr << "Invalid template ID: " << template_id << "\n";
		return false;
	}

	ifstream in(binary_path, ios::binary);
	if (!in) { cerr << "Cannot open binary template file: " << binary_path << "\n"; return false; }

	constexpr streamoff block_size = 25; // 2 * 10 * 10 bits, packed
	in.seekg((streamoff)template_id * block_size);
	if (!in) { cerr << "Invalid template ID or seek error (id=" << template_id << ")\n"; return false; }

	unsigned char buffer[block_size];
	in.read(reinterpret_cast<char*>(buffer), block_size);
	if (in.gcount() != block_size) {
		cerr << "Could not read a full template block for id " << template_id << " from " << binary_path
			 << " (got " << in.gcount() << " of " << block_size << " bytes)\n";
		return false;
	}

	int bit_index = 0;
	for (int sq = 0; sq < 2; ++sq)
		for (int i = 0; i < 10; ++i)
			for (int j = 0; j < 10; ++j) {
				int bit = (buffer[bit_index / 8] >> (bit_index % 8)) & 1;
				if (sq == 0) F0[i][j] = bit;
				else         F1[i][j] = bit;
				++bit_index;
			}

	return true;
}

// True when `s` is a nonempty run of digits, i.e. a record index into the binary file rather than a path.
static inline bool is_template_id(const string& s) {
	return !s.empty() && s.find_first_not_of("0123456789") == string::npos;
}

// -----------------------------------------------------------------------
// Validation: each row and column of F0/F1 must have a constant number of ones (that's what "frequency square" means), and that count becomes lambda2 / lambda3 respectively.
// -----------------------------------------------------------------------
static bool detect_lambda(const int F[10][10], const char* name, int& lambda_out) {
	int row_ones[10], col_ones[10] = {0};
	for (int i = 0; i < 10; ++i) {
		int c = 0;
		for (int j = 0; j < 10; ++j) { c += F[i][j]; col_ones[j] += F[i][j]; }
		row_ones[i] = c;
	}
	int lambda = row_ones[0];
	for (int i = 0; i < 10; ++i) {
		if (row_ones[i] != lambda) {
			cerr << "Invalid template: " << name << " row " << i << " has " << row_ones[i] << " ones, expected " << lambda << " (rows must be permutations of the same multiset).\n";
			return false;
		}
	}
	for (int j = 0; j < 10; ++j) {
		if (col_ones[j] != lambda) {
			cerr << "Invalid template: " << name << " column " << j << " has " << col_ones[j] << " ones, expected " << lambda << " (columns must be permutations of the same multiset).\n";
			return false;
		}
	}
	lambda_out = lambda;
	return true;
}

// -----------------------------------------------------------------------
// Graph construction
// -----------------------------------------------------------------------
struct BuiltGraph {
	vector<size_t> v;
	vector<int> d;
	vector<int> e;
	sparsegraph sg;
};

static BuiltGraph build_graph(const int F0[10][10], const int F1[10][10]) {
	vector<vector<int>> adj(N_NAUTY);

	auto add_edge = [&](int a, int b) {
		adj[a].push_back(b);
		adj[b].push_back(a);
	};

	for (int r = 0; r < 10; ++r) add_edge(ROW_HUB, ROW_BASE + r);
	for (int c = 0; c < 10; ++c) add_edge(COL_HUB, COL_BASE + c);
	add_edge(F0_HUB, F0_BASE + 0);
	add_edge(F0_HUB, F0_BASE + 1);
	add_edge(F1_HUB, F1_BASE + 0);
	add_edge(F1_HUB, F1_BASE + 1);

	for (int i = 0; i < 10; ++i) {
		for (int j = 0; j < 10; ++j) {
			int cell = cell_vertex(i, j);
			add_edge(cell, ROW_BASE + i);
			add_edge(cell, COL_BASE + j);
			add_edge(cell, F0_BASE + F0[i][j]);
			add_edge(cell, F1_BASE + F1[i][j]);
		}
	}

	BuiltGraph g;
	g.v.resize(N_NAUTY);
	g.d.resize(N_NAUTY);
	size_t off = 0;
	for (int i = 0; i < N_NAUTY; ++i) {
		g.v[i] = off;
		g.d[i] = (int)adj[i].size();
		off += adj[i].size();
	}
	g.e.resize(off);
	for (int i = 0; i < N_NAUTY; ++i)
		copy(adj[i].begin(), adj[i].end(), g.e.begin() + g.v[i]);

	SG_INIT(g.sg);
	g.sg.nv = N_NAUTY;
	g.sg.nde = (int)off;
	g.sg.v = g.v.data();
	g.sg.d = g.d.data();
	g.sg.e = g.e.data();
	g.sg.vlen = N_NAUTY;
	g.sg.dlen = N_NAUTY;
	g.sg.elen = (int)off;
	g.sg.w = nullptr;
	g.sg.wlen = 0;
	return g;
}

// -----------------------------------------------------------------------
// Initial partition: this is what encodes the four allowed template isomorphism operations (and rules out anything else).
//
//   {ROW_HUB, COL_HUB}            	-- lets transpose be considered
//   {F0_HUB, F1_HUB}               -- lets square-swap be considered
//   relational rows / non-rel rows -- row perms must preserve this split
//   relational cols / non-rel cols -- col perms must preserve this split
//   {F0=1 node, F1=1 node}         -- "relational" symbol value, shared
//   {F0=0 node, F1=0 node}         -- "non-relational" symbol value, shared
//   all 100 cell nodes             -- free
// -----------------------------------------------------------------------
static void build_partition(int lambda_row, int lambda_col, int lab[N_NAUTY], int ptn[N_NAUTY]) {
	int pos = 0;
	auto add_cell = [&](const vector<int>& members) {
		for (size_t k = 0; k < members.size(); ++k) {
			lab[pos] = members[k];
			ptn[pos] = (k + 1 < members.size()) ? 1 : 0;
			++pos;
		}
	};

	add_cell({ROW_HUB, COL_HUB});
	add_cell({F0_HUB, F1_HUB});

	// Relational rows and columns must share a color class so that a transpose can exchange them.
	{
		vector<int> rel;
		for (int r = 0; r < lambda_row; ++r) rel.push_back(ROW_BASE + r);
		for (int c = 0; c < lambda_col; ++c) rel.push_back(COL_BASE + c);
		if (!rel.empty()) add_cell(rel);
	}

	// Likewise for non-relational rows and columns.
	{
		vector<int> nrel;
		for (int r = lambda_row; r < 10; ++r) nrel.push_back(ROW_BASE + r);
		for (int c = lambda_col; c < 10; ++c) nrel.push_back(COL_BASE + c);
		if (!nrel.empty()) add_cell(nrel);
	}

	add_cell({F0_BASE + 1, F1_BASE + 1});
	add_cell({F0_BASE + 0, F1_BASE + 0});

	{
		vector<int> cells; cells.reserve(100);
		for (int p = 0; p < 100; ++p) cells.push_back(CELL_BASE + p);
		add_cell(cells);
	}

	if (pos != N_NAUTY) {
		cerr << "Internal error: partition covers " << pos << " of " << N_NAUTY << " vertices\n";
		exit(1);
	}
}

// -----------------------------------------------------------------------
// Automorphism capture + decoding
// -----------------------------------------------------------------------
static vector<array<int, N_NAUTY>> g_generators;

static void userautomproc(int /*count*/, int* perm, int* /*orbits*/, int /*numorbits*/, int /*stabvertex*/, int n) {
	array<int, N_NAUTY> p;
	for (int i = 0; i < n; ++i) p[i] = perm[i];
	g_generators.push_back(p);
}

struct DecodedTemplateAuto {
	bool transpose;           // rows <-> columns
	bool swap_squares;        // F0 <-> F1
	array<int, 10> row_dest;  // row_dest[i] = destination index within its destination block
	array<int, 10> col_dest;
	array<int, 100> point_perm; // point_perm[i*10+j] = i'*10+j'
};

static DecodedTemplateAuto decode(const array<int, N_NAUTY>& perm) {
	DecodedTemplateAuto d{};
	d.transpose    = (perm[ROW_HUB] == COL_HUB);
	d.swap_squares = (perm[F0_HUB] == F1_HUB);

	for (int i = 0; i < 10; ++i) {
		int dst = perm[ROW_BASE + i];
		d.row_dest[i] = (dst >= ROW_BASE && dst < ROW_BASE + 10) ? (dst - ROW_BASE) : (dst - COL_BASE);
	}
	for (int j = 0; j < 10; ++j) {
		int dst = perm[COL_BASE + j];
		d.col_dest[j] = (dst >= COL_BASE && dst < COL_BASE + 10) ? (dst - COL_BASE) : (dst - ROW_BASE);
	}
	for (int i = 0; i < 10; ++i)
		for (int j = 0; j < 10; ++j) {
			int dst = perm[cell_vertex(i, j)] - CELL_BASE;
			d.point_perm[i * 10 + j] = dst;
		}
	return d;
}

static string perm_to_cycles(const array<int,10>& p) {
	array<bool,10> seen{};
	ostringstream out;
	for (int i = 0; i < 10; ++i) {
		if (seen[i] || p[i] == i) { seen[i] = true; continue; }
		out << "(";
		int j = i; bool first = true;
		while (!seen[j]) { seen[j] = true; if (!first) out << " "; out << j; first = false; j = p[j]; }
		out << ")";
	}
	string s = out.str();
	return s.empty() ? "()" : s;
}

static void print_automorphism(int idx, const DecodedTemplateAuto& d) {
	cout << "Automorphism #" << idx << "\n";
	cout << "  transpose (row<->col):      " << (d.transpose ? "yes" : "no") << "\n";
	cout << "  swap squares (F0<->F1):     " << (d.swap_squares ? "yes" : "no") << "\n";
	cout << "  row permutation" << (d.transpose ? " (rows -> destination columns)" : "") << ": " << perm_to_cycles(d.row_dest) << "\n";
	cout << "  col permutation" << (d.transpose ? " (cols -> destination rows)" : "") << ": " << perm_to_cycles(d.col_dest) << "\n";
	int moved = 0;
	for (int p = 0; p < 100; ++p) if (d.point_perm[p] != p) ++moved;
	cout << "  points moved: " << moved << " / 100\n\n";
}

// -----------------------------------------------------------------------
// Group closure: expand generators nauty found into the full, explicit automorphism group by repeatedly composing known elements with generators. 
// Each resulting permutation is independently re-verified against the actual graph adjacency.
// -----------------------------------------------------------------------
using Perm = array<int, N_NAUTY>;

static Perm identity_perm() {
	Perm p;
	for (int i = 0; i < N_NAUTY; ++i) p[i] = i;
	return p;
}

static Perm compose(const Perm& a, const Perm& b) {
	// (a after b): result[x] = a[b[x]]
	Perm r;
	for (int i = 0; i < N_NAUTY; ++i) r[i] = a[b[i]];
	return r;
}

// Independent structural verification: perm must preserve adjacency of the actual built graph.
static bool is_graph_automorphism(const Perm& perm, const BuiltGraph& g) {
	static vector<vector<char>> adj; // memoized adjacency matrix, built once
	if (adj.empty()) {
		adj.assign(N_NAUTY, vector<char>(N_NAUTY, 0));
		for (int u = 0; u < N_NAUTY; ++u) {
			size_t base = g.v[u];
			int deg = g.d[u];
			for (int k = 0; k < deg; ++k) adj[u][g.e[base + k]] = 1;
		}
	}
	for (int u = 0; u < N_NAUTY; ++u) {
		size_t base = g.v[u];
		int deg = g.d[u];
		for (int k = 0; k < deg; ++k) {
			int v = g.e[base + k];
			if (!adj[perm[u]][perm[v]]) return false;
		}
	}
	return true;
}

struct PermHash {
	size_t operator()(const Perm& p) const {
		size_t h = 1469598103934665603ULL;
		for (int x : p) { h ^= (size_t)x; h *= 1099511628211ULL; }
		return h;
	}
};

// Returns the full group as a vector of verified permutations (includes the identity).
static vector<Perm> close_group(const vector<Perm>& generators, const BuiltGraph& g, long long expected_order, size_t hard_cap = 2000000) {
	unordered_set<Perm, PermHash> seen;
	vector<Perm> frontier;
	Perm id = identity_perm();
	seen.insert(id);
	frontier.push_back(id);

	vector<Perm> all;
	all.push_back(id);

	while (!frontier.empty()) {
		vector<Perm> next_frontier;
		for (const Perm& f : frontier) {
			for (const Perm& gen : generators) {
				Perm cand = compose(gen, f);
				if (seen.find(cand) == seen.end()) {
					seen.insert(cand);
					all.push_back(cand);
					next_frontier.push_back(cand);
					if (all.size() > hard_cap) {
						cerr << "Warning: group closure exceeded " << hard_cap << " elements; aborting early. Something is likely wrong (expected order was " << expected_order << ").\n";
						return all;
					}
				}
			}
		}
		frontier.swap(next_frontier);
	}

	// Independently verify every element found.
	for (const Perm& p : all) {
		if (!is_graph_automorphism(p, g)) {
			cerr << "FATAL: an element produced by group closure is NOT a valid graph automorphism. This indicates a bug (likely in compose() or in the generators). Aborting.\n";
			exit(1);
		}
	}

	return all;
}


// -----------------------------------------------------------------------

int main(int argc, char* argv[]) {
	if (argc < 2) {
		cerr << "Usage: " << argv[0] << " <template.txt | TEMPLATE_ID> [lambda_row] [lambda_col] [--bin <templates.bin>]\n"
			 << "  A numeric first argument selects that record of the packed binary template file (default " << DEFAULT_TEMPLATE_BIN << ");\n"
			 << "  anything else is read as a text template.\n"
			 << "  lambda_row/lambda_col default to 4 (type 4^4).\n";
		return 1;
	}

	string template_arg = argv[1];
	string binary_file  = DEFAULT_TEMPLATE_BIN;
	int lambda_row = 4, lambda_col = 4;

	// Positional lambdas are kept for compatibility; --bin may appear anywhere after the template argument
	int positional = 0;
	for (int i = 2; i < argc; ++i) {
		string arg = argv[i];
		if (arg == "--bin") {
			if (i + 1 >= argc) { cerr << "Missing value for --bin\n"; return 1; }
			binary_file = argv[++i];
			continue;
		}
		if (positional == 0)      lambda_row = atoi(arg.c_str());
		else if (positional == 1) lambda_col = atoi(arg.c_str());
		else { cerr << "Unrecognized argument: " << arg << "\n"; return 1; }
		++positional;
	}

	int F0[10][10], F1[10][10];
	if (is_template_id(template_arg)) {
		int template_id = atoi(template_arg.c_str());
		cout << "Template source: " << binary_file << " record " << template_id << "\n";
		if (!read_template_binary(binary_file, template_id, F0, F1)) return 1;
	} else {
		cout << "Template source: " << template_arg << "\n";
		if (!read_template(template_arg, F0, F1)) return 1;
	}

	int lambda2, lambda3;
	if (!detect_lambda(F0, "F0", lambda2)) return 1;
	if (!detect_lambda(F1, "F1", lambda3)) return 1;

	cout << "Detected type: lambda0(row)=" << lambda_row << ", lambda1(col)=" << lambda_col << ", lambda2(F0)=" << lambda2 << ", lambda3(F1)=" << lambda3 << "\n";
	if (lambda2 != lambda3) {
		cout << "Note: lambda2 != lambda3, so F0<->F1 swap can never be a valid automorphism (nauty will confirm this by finding none).\n";
	}
	if (lambda_row != lambda_col) {
		cout << "Note: lambda_row != lambda_col, so transpose can never be a valid automorphism.\n";
	}
	cout << "\n";

	BuiltGraph g = build_graph(F0, F1);

	int lab[N_NAUTY], ptn[N_NAUTY], orbits[N_NAUTY];
	build_partition(lambda_row, lambda_col, lab, ptn);

	DEFAULTOPTIONS_SPARSEGRAPH(options);
	options.getcanon      = TRUE;
	options.defaultptn    = FALSE;
	options.writeautoms   = FALSE;
	options.writemarkers  = FALSE;
	options.userautomproc = userautomproc;

	statsblk stats;
	sparsegraph canon_sg;
	SG_INIT(canon_sg);

	g_generators.clear();
	sparsenauty(&g.sg, lab, ptn, orbits, &options, &stats, &canon_sg);

	cout << "Automorphism group order: " << stats.grpsize1;
	if (stats.grpsize2 != 0) cout << " * 10^" << stats.grpsize2;
	cout << "\n";
	cout << "Number of generators reported by nauty: " << g_generators.size() << "\n\n";

	cout << "--- Generators as reported by nauty (not yet closed into a full group) ---\n\n";
	for (size_t i = 0; i < g_generators.size(); ++i) {
		DecodedTemplateAuto d = decode(g_generators[i]);
		print_automorphism((int)i + 1, d);
	}

	// ---------------------------------------------------------------
	// Expand to the full, explicit, independently-verified group.
	// ---------------------------------------------------------------
	long long expected_order = (long long)stats.grpsize1; // fine unless grpsize2 != 0 (astronomically large group)
	if (stats.grpsize2 != 0) {
		cout << "Group order has a 10^" << stats.grpsize2 << " factor, too large to enumerate; skipping full closure.\n";
		return 0;
	}

	vector<Perm> gens(g_generators.begin(), g_generators.end());
	vector<Perm> full_group = close_group(gens, g, expected_order);

	cout << "==========================================================\n";
	cout << "Full automorphism group: " << full_group.size() << " elements (nauty reported order " << expected_order << "), "
		 << (full_group.size() == (size_t)expected_order ? "MATCH" : "MISMATCH!") << "\n";
	cout << "Every element below was independently re-verified against the graph adjacency.\n";
	cout << "==========================================================\n\n";

	if (full_group.size() != (size_t)expected_order) {
		cerr << "Warning: closure size does not match nauty's reported group order. Do not trust the listing below.\n";
	}

	if (full_group.size() <= 200) {
		for (size_t i = 0; i < full_group.size(); ++i) {
			DecodedTemplateAuto d = decode(full_group[i]);
			print_automorphism((int)i + 1, d);
		}
	} else {
		cout << "(" << full_group.size() << " elements verified but not printed individually; raise the threshold in the source if you want the full listing.)\n";
	}

	return 0;
}