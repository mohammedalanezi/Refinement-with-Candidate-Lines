#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <unordered_set>
#include <chrono>
#include <cstring>
#include <algorithm>
#include <filesystem>
#include <map>

#include "cadical.hpp"
#include "exhaustive.hpp"
#include "nauty.h"

namespace fs = std::filesystem;

std::unordered_set<std::string> certificates;
int template_count = 0;
int cert_count = 0;

// Binary file stream for all templates
std::ofstream binary_output;

// Precomputed variable index -> (layer, row, col)
struct VarIndexInfo { int8_t l, r, c; };  // l in 0..3, r,c in 0..9
static VarIndexInfo var_lookup[401];   // 1‑based, so size 401 (ignore index 0)

// ------------- Global timing accumulators -------------
std::chrono::duration<double> total_template_build{0.0};
std::chrono::duration<double> total_graph_build{0.0};
std::chrono::duration<double> total_isomorphism{0.0};
std::chrono::duration<double> total_cert_creation{0.0};
std::chrono::duration<double> total_file_write{0.0};

int count_template_build = 0;
int count_graph_build = 0;
int count_isomorphism = 0;
int count_cert_creation = 0;
int count_file_write = 0;

auto t_last_recorded = std::chrono::steady_clock::now(); 
// ------------------------------------------------------

static DEFAULTOPTIONS_GRAPH(options);
statsblk stats;

// Fixed constants for the nauty graph
constexpr int N_NAUTY = 128;
constexpr int M_NAUTY = (N_NAUTY + WORDSIZE - 1) / WORDSIZE;

// Precomputed base graph (edges independent of the template)
static setword base_graph[N_NAUTY * M_NAUTY] = {0};
static bool base_ready = false;

// Fixed initial ordered partition (copied before each densenauty call)
static int init_lab[N_NAUTY];
static int init_ptn[N_NAUTY];

// Reusable buffers, allocated once and reused
static setword* adj_reuse   = nullptr;   // adjacency matrix for current template
static setword* canon_reuse = nullptr;   // canonical form output

void init_base_graph() {
    if (base_ready) return;
    const int point_count = 99;
    const int R = 124, C = 125, S1 = 126, S2 = 127;

    // Cells to row/col vertices
    for (int r = 0; r < 10; ++r) {
        for (int c = 0; c < 10; ++c) {
            int id = r * 10 + c;
            ADDELEMENT(base_graph + id * M_NAUTY, point_count + r + 1);
            ADDELEMENT(base_graph + (point_count + r + 1) * M_NAUTY, id);
            ADDELEMENT(base_graph + id * M_NAUTY, point_count + 10 + c + 1);
            ADDELEMENT(base_graph + (point_count + 10 + c + 1) * M_NAUTY, id);
        }
        ADDELEMENT(base_graph + (point_count + r + 1) * M_NAUTY, R);
        ADDELEMENT(base_graph + R * M_NAUTY, point_count + r + 1);
        ADDELEMENT(base_graph + (point_count + 10 + r + 1) * M_NAUTY, C);
        ADDELEMENT(base_graph + C * M_NAUTY, point_count + 10 + r + 1);
    }

    // Symbol vertices to S1/S2 (vertices 120..123)
    ADDELEMENT(base_graph + (point_count + 20 + 1) * M_NAUTY, S1);
    ADDELEMENT(base_graph + S1 * M_NAUTY, point_count + 20 + 1);
    ADDELEMENT(base_graph + (point_count + 20 + 2) * M_NAUTY, S1);
    ADDELEMENT(base_graph + S1 * M_NAUTY, point_count + 20 + 2);
    ADDELEMENT(base_graph + (point_count + 20 + 3) * M_NAUTY, S2);
    ADDELEMENT(base_graph + S2 * M_NAUTY, point_count + 20 + 3);
    ADDELEMENT(base_graph + (point_count + 20 + 4) * M_NAUTY, S2);
    ADDELEMENT(base_graph + S2 * M_NAUTY, point_count + 20 + 4);

    base_ready = true;
}

void init_fixed_partition() {
    for (int i = 0; i < N_NAUTY; ++i) {
        init_lab[i] = i;
        init_ptn[i] = 1;
    }
    init_ptn[123] = 0;   // end of grey
    init_ptn[125] = 0;   // end of red
    init_ptn[127] = 0;   // end of blue
}

// Build the adjacency matrix for one template into a pre‑allocated buffer
void build_graph_fast(const int grid[2][10][10], setword* g) {
    memcpy(g, base_graph, N_NAUTY * M_NAUTY * sizeof(setword));

    const int point_count = 99;
    for (int r = 0; r < 10; ++r) {
        for (int c = 0; c < 10; ++c) {
            int id = r * 10 + c;
            int s1 = grid[0][r][c];
            int s2 = grid[1][r][c];
            ADDELEMENT(g + id * M_NAUTY, point_count + 20 + s1 + 1);
            ADDELEMENT(g + (point_count + 20 + s1 + 1) * M_NAUTY, id);
            ADDELEMENT(g + id * M_NAUTY, point_count + 20 + 2 + s2 + 1);
            ADDELEMENT(g + (point_count + 20 + 2 + s2 + 1) * M_NAUTY, id);
        }
    }
}

//    Create a 2x10x10 template from a solution_set line
using Grid2 = int[2][10][10];

void create_template_from_line(const std::vector<int>& line, Grid2& grid) {
	// initialise to -1
	for (int l = 0; l < 2; ++l)
		for (int y = 0; y < 10; ++y)
			for (int x = 0; x < 10; ++x)
				grid[l][y][x] = -1;

	bool dense = (line.size() == 400);
	for (int j = 0; j < 400; ++j) {
		int i = j + 1;
		const auto& info = var_lookup[i];
		if (info.l >= 2) {
			int s = 0;
			if (dense ? (line[i - 1] > 0) : (std::find(line.begin(), line.end(), i) != line.end()))
				s = 1;
			grid[info.l - 2][info.c][info.r] = s;
		}
	}
}

//    Canonical form to string (for uniqueness check)
std::string canon_to_string(const setword* canong, int n, int m) {
	return std::string(reinterpret_cast<const char*>(canong), n * m * sizeof(setword));
}

//    Generate template file
//    Write a template as 25 bytes to the global binary file
void generate_file(const int grid[2][10][10]) {
	auto t_start = std::chrono::steady_clock::now();   // FILE WRITE start

	unsigned char buffer[25] = {0};
	int bit_index = 0;
	for (int square = 0; square < 2; ++square)
		for (int row = 0; row < 10; ++row)
			for (int col = 0; col < 10; ++col) {
				int val = grid[square][row][col];
				if (val) {
					int byte_idx = bit_index / 8;
					int bit_pos  = bit_index % 8;
					buffer[byte_idx] |= (1 << bit_pos);
				}
				++bit_index;
			}
	if(bit_index != 200)
		std::cout << bit_index <<"\n";
	binary_output.write(reinterpret_cast<const char*>(buffer), 25);
	
    if (!binary_output) {
        std::cerr << "FATAL: write failed at certificate #" << cert_count << ". Disk full or I/O error.\n";
        // Optionally throw an exception or exit immediately
        std::exit(EXIT_FAILURE);
    }

	total_file_write += std::chrono::steady_clock::now() - t_start;
	count_file_write++;
}

//    Main processing of a single template
void process_template(const int grid[2][10][10]) {
    ++template_count;

    auto t_graph_start = std::chrono::steady_clock::now();

    // Allocate or reuse adjacency buffer
    if (!adj_reuse) adj_reuse = (setword*)calloc(N_NAUTY * M_NAUTY, sizeof(setword));
    build_graph_fast(grid, adj_reuse);

    auto t_graph_end = std::chrono::steady_clock::now();
    total_graph_build += t_graph_end - t_graph_start;
    count_graph_build++;

    // Fresh copy of the partition
    int lab[N_NAUTY], ptn[N_NAUTY];
    memcpy(lab, init_lab, sizeof(lab));
    memcpy(ptn, init_ptn, sizeof(ptn));

    // Allocate or reuse canonical buffer
    if (!canon_reuse) canon_reuse = (setword*)calloc(N_NAUTY * M_NAUTY, sizeof(setword));
    int orbits[N_NAUTY] = {0};

    densenauty(adj_reuse, lab, ptn, orbits, &options, &stats, M_NAUTY, N_NAUTY, canon_reuse);

    auto t_iso_end = std::chrono::steady_clock::now();
    total_isomorphism += t_iso_end - t_graph_end;
    count_isomorphism++;

    std::string cert = canon_to_string(canon_reuse, N_NAUTY, M_NAUTY);
    if (certificates.find(cert) == certificates.end()) {
        certificates.insert(cert);
        ++cert_count;

        auto t_cert_end = std::chrono::steady_clock::now();
        total_cert_creation += t_cert_end - t_iso_end;
        count_cert_creation++;

        generate_file(grid);
        if (cert_count % 100 == 0)
            std::cout << "new certificate, #" << cert_count << "\n";
    }
}

//    Read and process templates4444.txt
void process_templates4444(const std::string& filepath) {
	std::ifstream fin(filepath);
	if (!fin) {
		std::cerr << "Cannot open " << filepath << "\n";
		return;
	}

	Grid2 grid;
	int current_square = 0;
	int current_row = 0;
	std::string line;
	std::chrono::steady_clock::time_point build_start;
	bool building = false;

	while (std::getline(fin, line)) {
		// strip whitespace
		line.erase(std::remove_if(line.begin(), line.end(), ::isspace), line.end());
		if (line.empty()) continue;   // skip blank lines
		
		if (!building) {
			build_start = std::chrono::steady_clock::now();  // TEMPLATE BUILD start
			building = true;
		}

		std::vector<int> row;
		for (char ch : line) row.push_back(ch - '0');   // ASCII digit to int
		// append to current square
		for (int col = 0; col < 10; ++col)
			grid[current_square][current_row][col] = row[col];
		++current_row;

		if (current_square == 1 && current_row == 10) {
			auto build_end = std::chrono::steady_clock::now(); // TEMPLATE BUILD end
			total_template_build += build_end - build_start;
			count_template_build++;
			building = false;

			// complete template
			process_template(grid);
			// reset
			current_square = 0;
			current_row = 0;
		} else if (current_square == 0 && current_row == 10) {
			current_square = 1;
			current_row = 0;
		}
	}
}

constexpr int order            = 10;
constexpr int symbol_count     = 2;
constexpr int frequencies[2]   = {6, 4};
constexpr int frequency_squares = 4;
constexpr int seed             = 0;

// Helper: fresh auxiliary variable
static int var_cnt = 0;
static int new_var() { return ++var_cnt; }

// Variable indexing
static int get1DIndex(int l, int r, int c, int s) {
	int index = 4 * order * r + 4 * c + l + 1;
	if (s == 0)
		index = -index;
	return index;
}

// Clause construction helpers
static void addImplicationClause(CaDiCaL::Solver& solver, const std::vector<int>& antecedent, const std::vector<int>& consequent) {
	std::vector<int> clause;
	for (int x : antecedent)
		clause.push_back(-x);
	for (int y : consequent)
		clause.push_back(y);
	solver.clause(clause);
}

// Cardinality constraint (sequential counter encoding)
static void addCardinalityClauses(CaDiCaL::Solver &solver, const std::vector<int> &var_list, int min_val, int max_val) {
	int n = (int)var_list.size();
	int k = max_val + 1;   // at most max_val  -> forbid j == k
	int l = min_val;       // at least min_val -> enforce j == l for i=n

	// Allocate auxiliary variables s[i][j] (0 <= i <= n, 0 <= j <= k)
	int num_aux = (n + 1) * (k + 1);
	int need_max = var_cnt + num_aux;
	solver.resize(need_max);          // ensure the solver knows these variables

	std::vector<std::vector<int>> s(n + 1, std::vector<int>(k + 1));
	for (int i = 0; i <= n; ++i)
		for (int j = 0; j <= k; ++j)
			s[i][j] = ++var_cnt;       // assign new variable

	// 1) "0 variables are always true of variables x1..xi"
	for (int i = 0; i <= n; ++i) {
		solver.add(s[i][0]);
		solver.add(0);
	}

	// 2) "j >= 1 of nothing is always false"
	for (int j = 1; j <= k; ++j) {
		solver.add(-s[0][j]);
		solver.add(0);
	}

	// 3) Lower bound: at least min_val of all n variables must be true
	for (int j = 1; j <= l; ++j) {
		solver.add(s[n][j]);
		solver.add(0);
	}

	// 4) Upper bound: at most max_val -> never allow k = max_val+1 true
	for (int i = 1; i <= n; ++i) {
		solver.add(-s[i][k]);
		solver.add(0);
	}

	// 5) Propagation clauses
	for (int i = 1; i <= n; ++i)
		for (int j = 1; j <= k; ++j) {
			// s[i-1][j]  ->  s[i][j]
			solver.add(-s[i-1][j]);
			solver.add(s[i][j]);
			solver.add(0);

			// x_i ∧ s[i-1][j-1]  ->  s[i][j]
			solver.add(-var_list[i-1]);
			solver.add(-s[i-1][j-1]);
			solver.add(s[i][j]);
			solver.add(0);

			if (j <= l) {
				// s[i][j]  ->  s[i-1][j] ∨ x_i
				solver.add(-s[i][j]);
				solver.add(s[i-1][j]);
				solver.add(var_list[i-1]);
				solver.add(0);

				// s[i][j]  ->  s[i-1][j-1]
				solver.add(-s[i][j]);
				solver.add(s[i-1][j-1]);
				solver.add(0);
			}
		}
}

// Lexicographic ordering (vectors of length 3)
static void addLexicographicalOrder(CaDiCaL::Solver& solver, const std::vector<int>& a, const std::vector<int>& b) {
	addImplicationClause(solver, {a[0]}, {b[0]}); // a[0]=1 => b[0]=1  (i.e., -a[0] or b[0])

	for (int i = 0; i < 2; ++i) { // a[0]=b[0] => -a[1] or b[1] [parityA used to express equality]
		int parityA = i * 2 - 1; // -1, +1
		addImplicationClause(solver, {parityA * a[0], parityA * b[0]}, {-a[1], b[1]});

		for (int j = 0; j < 2; ++j) { // a[0]=b[0] and a[1]=b[1] => -a[2] or b[2]
			int parityB = j * 2 - 1;
			addImplicationClause(solver, {parityA * a[0], parityA * b[0], parityB * a[1], parityB * b[1]}, {-a[2], b[2]});
		}
	}
}

// Orthogonality clauses (only called for squares 2 and 3)
static void addOrthogonalityClauses(CaDiCaL::Solver& solver, int square1, int square2,
									const int* frequencies1, const int* frequencies2) {
	// freq_pairs[(x,y)][(s,t)] = auxiliary variable
	std::map<std::pair<int,int>, std::map<std::pair<int,int>, int>> freq_pairs;

	for (int s = 0; s < symbol_count; ++s)
		for (int t = 0; t < symbol_count; ++t) {
			int expected_orthogonality = frequencies1[s] * frequencies2[t];
			std::pair<int,int> point = {s, t};
			std::vector<int> point_pairs;

			for (int x = 0; x < order; ++x)
				for (int y = 0; y < order; ++y) {
					int pair_var = new_var();
					point_pairs.push_back(pair_var);
					freq_pairs[{x, y}][point] = pair_var;

					// pair_var -> square1(x,y,s) AND square2(x,y,t)
					addImplicationClause(solver, {pair_var}, {get1DIndex(square1, x, y, s)});
					addImplicationClause(solver, {pair_var}, {get1DIndex(square2, x, y, t)});

					// (square1(x,y,s) AND square2(x,y,t)) -> pair_var
					addImplicationClause(solver, {get1DIndex(square1, x, y, s), get1DIndex(square2, x, y, t)}, {pair_var});
				}
			// cardinality constraint: exactly expected_orthogonality of these pairs are true
			addCardinalityClauses(solver, point_pairs, expected_orthogonality, expected_orthogonality);
		}

	// Lemma 3.2 additional constraints (template specific)
	// Row/col constraints for the first 4 rows/cols (0..3)
	for (int x = 0; x < 4; ++x)
		for (int i = 0; i < 2; ++i) {
			// Row: frequencies of (i, 1-i) in rows 4..9 = 3
			std::vector<int> relation_ii_row;
			for (int y = 4; y < 10; ++y)
				relation_ii_row.push_back(freq_pairs[{x, y}][{i, 1 - i}]);
			addCardinalityClauses(solver, relation_ii_row, 3, 3);

			// Col: frequencies of (i, 1-i) in cols 4..9 = 3
			std::vector<int> relation_ii_col;
			for (int y = 4; y < 10; ++y)
				relation_ii_col.push_back(freq_pairs[{y, x}][{i, 1 - i}]);
			addCardinalityClauses(solver, relation_ii_col, 3, 3);
		}

	for (int x = 4; x < 10; ++x) { // Rows/cols 4..9
		{ // For (s=1, t=1): exactly 2 occurrences in rows 4..9
			std::vector<int> relation_iv_row;
			for (int y = 4; y < 10; ++y)
				relation_iv_row.push_back(freq_pairs[{x, y}][{1, 1}]);
			addCardinalityClauses(solver, relation_iv_row, 2, 2);

			std::vector<int> relation_iv_col;
			for (int y = 4; y < 10; ++y)
				relation_iv_col.push_back(freq_pairs[{y, x}][{1, 1}]);
			addCardinalityClauses(solver, relation_iv_col, 2, 2);
		} { // For (s=0, t=0): exactly 4 occurrences in rows 4..9
			std::vector<int> relation_iv_row;
			for (int y = 4; y < 10; ++y)
				relation_iv_row.push_back(freq_pairs[{x, y}][{0, 0}]);
			addCardinalityClauses(solver, relation_iv_row, 4, 4);

			std::vector<int> relation_iv_col;
			for (int y = 4; y < 10; ++y)
				relation_iv_col.push_back(freq_pairs[{y, x}][{0, 0}]);
			addCardinalityClauses(solver, relation_iv_col, 4, 4);
		}
		// For (i, 1-i): exactly 2 occurrences in all rows/cols 0..9
		for (int i = 0; i < 2; ++i) {
			std::vector<int> relation_iv_row;
			for (int y = 0; y < 10; ++y)
				relation_iv_row.push_back(freq_pairs[{x, y}][{i, 1 - i}]);
			addCardinalityClauses(solver, relation_iv_row, 2, 2);

			std::vector<int> relation_iv_col;
			for (int y = 0; y < 10; ++y)
				relation_iv_col.push_back(freq_pairs[{y, x}][{i, 1 - i}]);
			addCardinalityClauses(solver, relation_iv_col, 2, 2);
		}
	}
}

// Main encoding function
void create_encoding(CaDiCaL::Solver& solver) {
	// Initialise next variable index (all grid variables are pre‑allocated)
	var_cnt = std::abs(get1DIndex(frequency_squares - 1, order - 1, order - 1, symbol_count - 1));

	// --- Row and column cardinality constraints ---
	for (int l = 2; l < frequency_squares; ++l) {
		// Row constraints
		for (int x = 0; x < order; ++x)
			for (int z = 0; z < symbol_count; ++z) {
				std::vector<int> row_vars;
				for (int y = 0; y < order; ++y)
					row_vars.push_back(get1DIndex(l, x, y, z));
				addCardinalityClauses(solver, row_vars, frequencies[z], frequencies[z]);
			}
		// Column constraints
		for (int y = 0; y < order; ++y)
			for (int z = 0; z < symbol_count; ++z) {
				std::vector<int> col_vars;
				for (int x = 0; x < order; ++x)
					col_vars.push_back(get1DIndex(l, x, y, z));
				addCardinalityClauses(solver, col_vars, frequencies[z], frequencies[z]);
			}
	}

	// --- Template‑specific constraints---
	// Lexicographic orderings for square 2 (columns 5‑9)
	{
		std::vector<int> a(3), b(3), c(3);
		for (int y = 0; y < 3; ++y) {
			a[y] = get1DIndex(2, y+1, 5, 1);
			b[y] = get1DIndex(2, y+1, 6, 1);
			c[y] = get1DIndex(2, y+1, 7, 1);
		}
		addLexicographicalOrder(solver, a, b);

		for (int y = 0; y < 3; ++y) {
			a[y] = get1DIndex(2, y+1, 8, 1);
			b[y] = get1DIndex(2, y+1, 9, 1);
			c[y] = get1DIndex(2, y+1, 7, 1); // c redefined to column 7
		}
		addLexicographicalOrder(solver, a, b);
		addLexicographicalOrder(solver, b, c);
	}
	// Rows 5‑6 and 8‑9 (square 2, rows with indices 4..9 in 0‑based)
	for (int i = 0; i < 2; ++i) {
		std::vector<int> a(3), b(3), c(3);
		for (int x = 0; x < 3; ++x) {
			a[x] = get1DIndex(2, 4 + 3*i, x+1, 1);
			b[x] = get1DIndex(2, 5 + 3*i, x+1, 1);
			c[x] = get1DIndex(2, 6 + 3*i, x+1, 1);
		}
		addLexicographicalOrder(solver, a, b);
		addLexicographicalOrder(solver, b, c);
	}

	// Fixed values for squares 0 and 1
	for (int x = 0; x < order; ++x)
		for (int y = 0; y < order; ++y) {
			if (x < 4)
				solver.clause(get1DIndex(1, x, y, 1));
			else
				solver.clause(get1DIndex(1, x, y, 0));

			if (y < 4)
				solver.clause(get1DIndex(0, x, y, 1));
			else
				solver.clause(get1DIndex(0, x, y, 0));

			if (x == y && x < 4) {
				solver.clause(get1DIndex(2, x, y, 1));
				solver.clause(get1DIndex(3, x, y, 1));
			} else if (x < 4 && y < 4) {
				solver.clause(get1DIndex(2, x, y, 0));
				solver.clause(get1DIndex(3, x, y, 0));
			}
		}

	// Orthogonality between squares 2 and 3
	addOrthogonalityClauses(solver, 2, 3, frequencies, frequencies);

	// Additional unit clauses for specific cells
	for (int x = 4; x < 7; ++x) {
		solver.clause(get1DIndex(3, 0, x, 1));
		solver.clause(get1DIndex(3, x, 0, 1));
	}
	for (int x = 7; x < 10; ++x) {
		solver.clause(get1DIndex(2, 0, x, 1));
		solver.clause(get1DIndex(2, x, 0, 1));
	}
	solver.clause(get1DIndex(3, 1, 4, 1));
	solver.clause(get1DIndex(2, 2, 4, 1));
	solver.clause(get1DIndex(2, 3, 4, 1));
}

struct TemplatePolicy {
	mutable long int sol_count = 0;

	explicit operator bool() const { return true; }

	bool operator()(const std::vector<int>& solution) const {
        auto t_build_start = std::chrono::steady_clock::now();

        // Build grid directly
        int grid[2][10][10];
        std::memset(grid, -1, sizeof(grid));
        bool var_true[401] = {false};
        for (int v : solution)
            if (v > 0 && v <= 400)
                var_true[v] = true;

        for (int i = 1; i <= 400; ++i) {
            const auto& info = var_lookup[i];
            if (info.l >= 2)
                grid[info.l - 2][info.c][info.r] = var_true[i] ? 1 : 0;
        }

        auto t_build_end = std::chrono::steady_clock::now();
        total_template_build += t_build_end - t_build_start;
        count_template_build++;

        // The rest is identical to process_template, but inline for one less function call
        auto t_graph_start = std::chrono::steady_clock::now();

        if (!adj_reuse) adj_reuse = (setword*)calloc(N_NAUTY * M_NAUTY, sizeof(setword));
        build_graph_fast(grid, adj_reuse);

        auto t_graph_end = std::chrono::steady_clock::now();
        total_graph_build += t_graph_end - t_graph_start;
        count_graph_build++;

        int lab[N_NAUTY], ptn[N_NAUTY];
        memcpy(lab, init_lab, sizeof(lab));
        memcpy(ptn, init_ptn, sizeof(ptn));

        if (!canon_reuse) canon_reuse = (setword*)calloc(N_NAUTY * M_NAUTY, sizeof(setword));
        int orbits[N_NAUTY] = {0};
        densenauty(adj_reuse, lab, ptn, orbits, &options, &stats, M_NAUTY, N_NAUTY, canon_reuse);

        auto t_iso_end = std::chrono::steady_clock::now();
        total_isomorphism += t_iso_end - t_graph_end;
        count_isomorphism++;

        std::string cert = canon_to_string(canon_reuse, N_NAUTY, M_NAUTY);
        if (certificates.find(cert) == certificates.end()) {
            certificates.insert(cert);
            ++cert_count;

            auto t_cert_end = std::chrono::steady_clock::now();
            total_cert_creation += t_cert_end - t_iso_end;
            count_cert_creation++;

            generate_file(grid);
            if (cert_count % 100 == 0)
                std::cout << "new certificate, #" << cert_count << "\n";
        }

        if (++sol_count % 15000 == 0)
            std::cout << sol_count << " template solutions processed (" << std::chrono::duration<double>(std::chrono::steady_clock::now() - t_last_recorded).count() << "s)\n";
        return true;
	}

	static constexpr bool notifyAssignment = false;
	static constexpr bool earlyClause      = false;
	static constexpr bool minimizeClause   = false;
};

int find_solutions() {
	auto timer = std::chrono::steady_clock::now();
	static int max_var = std::abs(get1DIndex(frequency_squares - 1, order - 1, order - 1, symbol_count - 1));
	static std::vector<int> observe;
	for(int i = 0; i < max_var; i++)
		observe.push_back(i + 1);
	
	ExhaustiveSearchOptions templateOptions;
	templateOptions.to_observe = observe;
	templateOptions.only_neg = true;
	templateOptions.can_forget = true; // do not need forget on, but takes extremely long with it off

	CaDiCaL::Solver solver;
	solver.set("inprocessing", 0); 
	//solver.set("report",       1);
	solver.set("factor",       0);
	solver.set("factorcheck",  0);
	solver.declare_more_variables(max_var);
	create_encoding(solver);
	ExhaustiveSearch<TemplatePolicy> propagator(&solver, templateOptions);
	solver.solve(); 
	std::cout << propagator.get_solution_count() << " template solutions found and tested in ";
	std::cout << std::chrono::duration<double>(std::chrono::steady_clock::now() - timer).count() << "s\n";
	return propagator.get_solution_count();
}

int main() {
    auto start_time = std::chrono::steady_clock::now();
    memset(&stats, 0, sizeof(stats));

	binary_output.exceptions(std::ios::failbit | std::ios::badbit);
    binary_output.open("templates.bin", std::ios::binary | std::ios::out);
    if (!binary_output) {
        std::cerr << "Cannot open templates.bin for writing\n";
        return 1;
    }

    // Precompute variable index lookup
    for (int v = 1; v <= 400; ++v) {
        int idx = v - 1;
        var_lookup[v].r = idx / (4 * 10);
        int rem = idx % (4 * 10);
        var_lookup[v].c = rem / 4;
        var_lookup[v].l = rem % 4;
    }

    // One‑time nauty setup
    init_base_graph();
    init_fixed_partition();
    nauty_check(WORDSIZE, M_NAUTY, N_NAUTY, NAUTYVERSIONID);
    options.getcanon = TRUE;
    options.writeautoms = FALSE;
    options.writemarkers = FALSE;

    // Process existing templates from file
    process_templates4444("templates4444.txt");
    std::cout << "Certificates after file: " << certificates.size() << "\n";

	// To ensure that early termination of SAT doesn't stop the last 77 templates from being written 
    binary_output.flush();

    // Run SAT search
    int solutions = find_solutions();

    binary_output.close();
	if (binary_output.fail()) {
		std::cerr << "Error closing templates.bin, data may be incomplete.\n";
		return 1;
	}

    std::cout << "Total certificate count: " << certificates.size() << "\n";
	
	// -------------------- Timing summary --------------------
	std::cout << "\n===== Timing Summary =====\n";
	std::cout << std::fixed << std::setprecision(6);

	auto print_avg = [](const std::string& name, const std::chrono::duration<double>& total, int count) {
		std::cout << name << ": total " << total.count() << "s, " << count << " calls";
		if (count > 0)
			std::cout << ", avg " << (total.count() / count) << "s";
		std::cout << "\n";
	};

	auto end_time = std::chrono::steady_clock::now();
	auto elapsed = std::chrono::duration<double>(end_time - start_time);

	print_avg("Template build		", total_template_build, count_template_build);
	print_avg("Graph build   		", total_graph_build, count_graph_build);
	print_avg("Isomorphism   		", total_isomorphism, count_isomorphism);
	print_avg("Certificate creation	", total_cert_creation, count_cert_creation);
	print_avg("File write    		", total_file_write, count_file_write);
	print_avg("SAT Solve    		:", elapsed - (total_template_build + total_graph_build + total_isomorphism + total_cert_creation + total_file_write), solutions);
	std::cout << "\nTotal elapsed: " << elapsed.count() << " seconds\n";

	return 0;
}