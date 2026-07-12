#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <unordered_map>
#include <string>
#include <cstring>
#include <tuple>
#include <chrono>

#ifndef TRACK_TIME
#define TRACK_TIME 1
#endif

#ifndef WRITE_REFINEMENTS
#define WRITE_REFINEMENTS 0
#endif

using namespace std;

// Global data structures
#ifndef ORDER_DEFINED
#define ORDER_DEFINED
const int order = 10;
#endif

auto start_time = chrono::steady_clock::now();

uint64_t* intersects_once_BA = nullptr;
int rows_B = 0;
int* all_line_indices_A = nullptr;

long skipped_partial_solutions = 0;
long partial_count = 0;
long total_refinements = 0;
int count_A = 0;
int count_B = 0;

int last_word_bits = 0;
uint64_t last_word_mask = 0;

__uint128_t all_points_mask; // bit (p-1) set means point p is on this line (points 1–100, so bits 0–99 used)

vector<__uint128_t> cand_masks_A; 
vector<__uint128_t> cand_masks_B;

string output_path;
std::ofstream outfile;

static int* intersecting_B_buf = nullptr;

const vector<vector<vector<int>>> trivialTemplate = { {
 {1, 1, 1, 1, 1, 1, 1, 1, 1, 1},
 {1, 1, 1, 1, 1, 1, 1, 1, 1, 1},
 {1, 1, 1, 1, 1, 1, 1, 1, 1, 1},
 {1, 1, 1, 1, 1, 1, 1, 1, 1, 1},
 {0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
 {0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
 {0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
 {0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
 {0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
 {0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
{{1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
 {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
 {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
 {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
 {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
 {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
 {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
 {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
 {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
 {1, 1, 1, 1, 0, 0, 0, 0, 0, 0}}};

#if TRACK_TIME == 1 
double candidate_find_time = 0.0;
double precompute_time = 0.0;

double total_line_intersection_time = 0.0;
double total_line_covering_time = 0.0;

double total_refinement_early_blocking = 0.0;
double total_refinement_solve_time = 0.0;
#endif

struct U128Hash {
	size_t operator()(__uint128_t v) const {
		uint64_t lo = (uint64_t)v;
		uint64_t hi = (uint64_t)(v >> 64);
		// MurmurHash inspired finalizer
		lo ^= lo >> 33; 
		lo *= 0xff51afd7ed558ccdULL; 
		lo ^= lo >> 33;

		hi ^= hi >> 33; 
		hi *= 0xc4ceb9fe1a85ec53ULL; 
		hi ^= hi >> 33;
		return lo ^ (hi * 0x9e3779b97f4a7c15ULL);
	}
};

unordered_map<__uint128_t, int, U128Hash> cand_hash_A;

struct VarInfo { int8_t sq, r, c, s; }; // 4 bytes per entry
VarInfo var_lookup[2 * order * order * order + 1]; // index by var (1-based)

/**
 * @brief Reverses a SAT variable encoding into (square, row, col, symbol) tuple.
 * SAT variables are assigned in row-major order across two squares, with the innermost dimension being symbol.
 * @param var_index   1-based SAT variable index.
 * @param num_squares Number of squares.
 * @param num_rows    Number of rows per square.
 * @param num_cols    Number of columns per square.
 * @param num_symbols Number of symbols per square.
 * @returns A tuple of (square, row, col, symbol), all 0-based.
 */
tuple<int,int,int,int> indexTo4Tuple(int var_index, int num_squares, int num_rows, int num_cols, int num_symbols) {
	int vars_per_square = num_rows * num_cols * num_symbols;
	int adjusted = var_index - 1;
	int square = adjusted / vars_per_square;
	int offset = adjusted % vars_per_square;
	int symbol = offset % num_symbols;
	int remainder = offset / num_symbols;
	int col = remainder % num_cols;
	int row = remainder / num_cols;
	return {square, row, col, symbol};
}

/**
 * @brief Constructs a 128-bit __uint128_t from a list of point indices (only 100 bits are used).
 * @param line A vector of point values in the range [1, 100]. Each value is converted to a 0-based bit index and set in the __uint128_t.
 * @returns A __uint128_t with bits set at each position corresponding to a point in line.
 */
__uint128_t make_mask(const vector<int>& line) {
	__uint128_t m = 0;
	for (int x : line)
		m |= ((__uint128_t)1 << (x - 1)); // convert 1-100 to bit index 0-99
	return m; 
}

/**
 * @brief Checks if two Masks intersect exactly once.
 * Uses bitwise operators on both halves of the masks to check if they are a power of 2.
 * @param m1 The first __uint128_t.
 * @param m2 The second __uint128_t.
 * @returns If m1 and m2 intersect once.
 */
bool intersectsExactlyOnce(__uint128_t m1, __uint128_t m2) {
	__uint128_t c = m1 & m2;
	return c != 0 && (c & (c - 1)) == 0;
}

/**
 * Writes a 100‑bit permutation mask as 5 bytes to a binary output stream.
 * The mask must have exactly one set bit per row and per column.
 */
void write_compact_line(std::ofstream &out, __uint128_t mask) {
	uint8_t buf[5] = {0}; // zero-initialise, we will fill nibbles

	for (int row = 0; row < 10; ++row) {
		uint16_t row_bits = (mask >> (row * 10)) & 0x3FF; // Extract the 10 bits of this row
		int col = __builtin_ctz(row_bits); // Since the mask is a valid permutation, exactly one bit is set

		int byte_idx = row / 2;
		if (row % 2 == 0)
			buf[byte_idx] = col;		 // low nibble
		else
			buf[byte_idx] |= (col << 4); // high nibble
	}

	out.write(reinterpret_cast<const char*>(buf), 5);
}

/**
 * Writes a single 0xFF byte as a block separator.
 */
void write_separator(std::ofstream &out) {
	uint8_t sep = 0xFF;
	out.write(reinterpret_cast<const char*>(&sep), 1);
}

/**
 * Flush the output file.
 */
void flush_output() {
	outfile.flush();
}

struct CandidatePolicy { 
	mutable int is_A = false;
	explicit operator bool() const { return true; }
	bool operator()(const std::vector<int>& solution) const {
		if(is_A)
			cand_masks_A.push_back(make_mask(solution));
		else
			cand_masks_B.push_back(make_mask(solution));
		return true;
	}
	static constexpr bool notifyAssignment = false;
	static constexpr bool earlyClause = false;
	static constexpr bool minimizeClause = false;
};

static void addCardinalityClauses(CaDiCaL::Solver &solver, const std::vector<int> &var_list, int min_val, int max_val, int &var_cnt) {
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

static int getTemplateBit(const vector<vector<vector<int>>> tmpl, int r, int c, int bit) {
	if (bit >= 2)
		return tmpl[bit - 2][r][c];
	else
		return trivialTemplate[bit][r][c];
}

static void createCandidateEncoding(CaDiCaL::Solver &solver, const vector<vector<vector<int>>> tmpl, bool isRelational, int frequencySquare) {
	solver.declare_more_variables(100);
	int variable_count = 100; 
	int number_bits = tmpl.size() + trivialTemplate.size();

	for(int r = 0; r < order; r++) {
		vector<int> row_vars(10);
		vector<int> col_vars(10);
		for(int c = 0; c < order; c++) {
			row_vars[c] = r * order + c + 1;
			col_vars[c] = c * order + r + 1;
		}
		addCardinalityClauses(solver, row_vars, 1, 1, variable_count);
		addCardinalityClauses(solver, col_vars, 1, 1, variable_count);
	}

	unordered_map<int, vector<int>> weightBuckets;
	for(int weight = 0; weight < number_bits; weight++)
		weightBuckets[weight] = {};
		
	for(int r = 0; r < order; r++) // only include relational or non-relation points
		for(int c = 0; c < order; c++) {
			int weight = 0;
			for(int i = 0; i < number_bits; i++)
				weight += getTemplateBit(tmpl, r, c, i);
			if(isRelational) {
				if(getTemplateBit(tmpl, r, c, frequencySquare) == 0)
					solver.clause(-(r * order + c + 1));
				else
					weightBuckets[weight].push_back(r * order + c + 1);
			} else { 
				if(getTemplateBit(tmpl, r, c, frequencySquare) == 1)
					solver.clause(-(r * order + c + 1));
				else
					weightBuckets[weight].push_back(r * order + c + 1);
			}
		}
	
	if(isRelational) {
		if (weightBuckets[4].size() > 0)
			addCardinalityClauses(solver, weightBuckets[4], 1, 1, variable_count);  // exactly one weight-4
		if (weightBuckets[2].size() > 0)
			addCardinalityClauses(solver, weightBuckets[2], 9, 9, variable_count);  // exactly nine weight-2
	} else {
		if (weightBuckets[2].size() > 0)
			addCardinalityClauses(solver, weightBuckets[2], 6, 6, variable_count);  // exactly six weight-2
		if (weightBuckets[0].size() > 0)
			addCardinalityClauses(solver, weightBuckets[0], 4, 4, variable_count);  // exactly four weight-0
	}
}

void find_candidate_lines(const vector<vector<vector<int>>> tmpl, const bool isSecond) { // isSecond = true -> second square, false -> third square
#if TRACK_TIME == 1
	auto timer = chrono::steady_clock::now();
#endif
	CaDiCaL::Solver relationalCandidateSolver;
	CaDiCaL::Solver nonRelationalCandidateSolver;

	static vector<int> candidateObserve(100);
	for(int i = 0; i < 100; i++)
		candidateObserve[i] = i+1;
	
	ExhaustiveSearchOptions candidateOptions;
	candidateOptions.to_observe = candidateObserve;
	candidateOptions.only_neg = true;
	
	int frequencySquare = isSecond ? 2 : 3;
	createCandidateEncoding(relationalCandidateSolver, tmpl, true, frequencySquare);
	createCandidateEncoding(nonRelationalCandidateSolver, tmpl, false, frequencySquare);

	CandidatePolicy candidatePolicy;
	candidatePolicy.is_A = isSecond;

	ExhaustiveSearch<CandidatePolicy> relationalCandidatePropagator(&relationalCandidateSolver, candidateOptions, candidatePolicy);
	ExhaustiveSearch<CandidatePolicy> nonRelationalCandidatePropagator(&nonRelationalCandidateSolver, candidateOptions, candidatePolicy);

	relationalCandidateSolver.solve();
	nonRelationalCandidateSolver.solve();
	
	if(isSecond)
		count_A = cand_masks_A.size();
	else
		count_B = cand_masks_B.size();

	cout << "		Found " << (isSecond ? count_A : count_B) << " candidate lines for square " << (isSecond ? "2" : "3");
	
#if TRACK_TIME == 1
	cout << " in " << chrono::duration<double>(chrono::steady_clock::now() - timer).count() << "s\n";
#else
	cout << "\n";
#endif
}

/**
 * @brief Precomputes all data structures needed for fast per-solution filtering and SAT encoding.
 *
 * Builds four bitset tables, all in flat row-major layout where each row is a bitset over the lines of one square packed into 64-bit words:
 *
 *  - `intersects_once_BA[i * rows_B + w]`: bit j set iff B line j intersects A line i exactly once
 *
 * With ~14k lines per side, intersects_once_AB/BA are ~24MB each.Both fit in L3 cache, keeping the bit lookups fast across all tens of millions of calls.
 *
 * Also initialises:
 * 
 *  - `all_line_indices_A/B`: identity index arrays [0, 1, ..., count-1] used as the default candidate set when no filtering has been applied.
 * 
 *  - `var_lookup`: int to 4 tuple look up map, used to avoid needing to divide multiple times per line.
 */
void precomputeDataStructures() {
	auto start = chrono::steady_clock::now();

	all_points_mask = ((__uint128_t)1 << 100) - 1; // bits 0–99 set, one per grid point
	
	rows_B = (count_B + 63) / 64;
	intersects_once_BA = new uint64_t[(long long)count_A * rows_B](); // intersects_once_BA[j * rows_B + w]: bit i set iff B line i intersects A line j exactly once.

	for (int i = 0; i < count_A; ++i) 
		for (int j = 0; j < count_B; ++j) { // for every (A line i, B line j) pair, compute how many points they share
			if (intersectsExactlyOnce(cand_masks_A[i], cand_masks_B[j])) {
				// store pair as bit in row j of intersects_once_BA. Each row is `rows_B` 64-bit words wide, so row j starts at offset j*rows_B
				// line i defined in word i/64 of that row, at bit position i%64. Setting that bit says: B line i intersects A line j exactly once
				intersects_once_BA[(long long)i * rows_B + j / 64] |= (1ULL << (j % 64));
			}
		}

	all_line_indices_A = new int[count_A];
	for(int i = 0; i < count_A; i++)
		all_line_indices_A[i] = i;

	cand_hash_A.reserve(count_A * 2); // halves load factor so we have 2x fewer collision chains
	for (int i = 0; i < count_A; ++i)
		cand_hash_A[cand_masks_A[i]] = i;

	for (int var = 1; var <= 2 * order * order * order; var++) {
		auto [sq, r, c, s] = indexTo4Tuple(var, 2, order, order, order);
		var_lookup[var] = { (int8_t)sq, (int8_t)r, (int8_t)c, (int8_t)s };
	}
	
	intersecting_B_buf = new int[count_B];
	
	last_word_bits = count_B % 64;
	last_word_mask = last_word_bits ? (1ULL << last_word_bits) - 1 : ~0ULL;

	auto end = chrono::steady_clock::now();
	double elapsed = chrono::duration<double>(end - start).count();
	cout << "	Precomputed intersections using masks in " << elapsed << " seconds." << endl;
}

/**
 * @brief Filters candidate lines to those intersecting every opposite line exactly once.
 *
 * Uses precomputed bitset tables for efficiency. Each opposite line has a precomputed bitset row where bit i indicates that candidate line i satisfies
 * the intersection count constraint against that opposite line. AND over all opposite rows together yields a single bitset where bit i is set iff
 * candidate i satisfies the constraint against every opposite simultaneously.
 *
 * Complexity is O(opposite_count * words + line_count) bitwise operations.
 *
 * @param intersecting_indices Output array for indices that pass the filter. Must be pre-allocated to at least line_count.
 * @param intersection_count   Running count of indices written (modified in place).
 * @param line_indices         Candidate line indices to test.
 * @param line_count           Number of candidate lines to test.
 * @param opposite_indices     Indices of the opposite square's solution lines.
 * @param opposite_count       Number of opposite solution lines.
 * @param is_A                 If true, line_indices are A lines tested against B opposites; otherwise B lines tested against A opposites.
 * @param union_mask		   OR of all surviving candidate masks (used to skip the coverage recompute).
 */
void getIntersectingBLineIndices(int intersecting_indices[], int& intersection_count,
								const int opposite_indices[], __uint128_t& union_mask) { 
	const int    words       	 = rows_B;
	const uint64_t* bitset_table = intersects_once_BA;
	const auto&     masks        = cand_masks_B;

	uint64_t* result = (uint64_t*)alloca(words * sizeof(uint64_t));
	bool resultSet = false;

	for (int j = 0; j < order; j++)
		if (opposite_indices[j] >= 0) {
			if(!resultSet) {
				resultSet = true;
				memcpy(result, bitset_table + (long long)opposite_indices[j] * words, words * sizeof(uint64_t));
				continue;
			}
			const uint64_t* row = bitset_table + (long long)opposite_indices[j] * words;
			uint64_t nonzero = 0;
			for (int w = 0; w < words; ++w) {
				result[w] &= row[w];
				nonzero |= result[w]; // track whether anything remains set
			}
			if (!nonzero) { // Early exit: result already all-zero; nothing will pass
				intersection_count = 0;
				return;
			}
		}
	if (!resultSet) return;

	result[rows_B - 1] &= last_word_mask;
	for (int w = 0; w < rows_B; ++w) {
		uint64_t word = result[w];
		if (w == rows_B - 1)
			word &= last_word_mask;   // discard invalid bits
		while (word) {
			int bit = __builtin_ctzll(word);
			int idx = w * 64 + bit;
			intersecting_indices[intersection_count++] = idx;
			union_mask |= masks[idx];
			word &= word - 1;
		}
	}
}

void getIntersectingBCovering(const int opposite_indices[], __uint128_t& union_mask) {
	const int    words       	 = rows_B;
	const uint64_t* bitset_table = intersects_once_BA;
	const auto&     masks        = cand_masks_B;

	uint64_t* result = (uint64_t*)alloca(words * sizeof(uint64_t));
	bool resultSet = false;

	for (int j = 0; j < order; j++)
		if (opposite_indices[j] >= 0) {
			if(!resultSet) {
				resultSet = true;
				memcpy(result, bitset_table + (long long)opposite_indices[j] * words, words * sizeof(uint64_t));
				continue;
			}
			const uint64_t* row = bitset_table + (long long)opposite_indices[j] * words;
			uint64_t nonzero = 0;
			for (int w = 0; w < words; ++w) {
				result[w] &= row[w];
				nonzero |= result[w]; // track whether anything remains set
			}
			if (!nonzero) { // Early exit: result already all-zero; nothing will pass
				return;
			}
		}
	if (!resultSet) return;

	result[rows_B - 1] &= last_word_mask;
	for (int w = 0; w < rows_B; ++w) {
		uint64_t word = result[w];
		while (word) {
			int bit = __builtin_ctzll(word);
			int idx = w * 64 + bit;
			union_mask |= masks[idx];
			if (union_mask == all_points_mask) return;
			word &= word - 1;
		}
	}
}

/**
 * @brief Recursively counts the ways to select a subset of candidate lines that together form an exact cover of all 100 grid points.
 *
 * The search enumerates subsets of the candidate lines given by `B_indices` (from index `idx` to `B_count-1`).  At each step the function considers the
 * current line `idx` and branches into two possibilities: skip it or, if it does not overlap with already covered points, include it. The recursion stops
 * when all points are covered (success) or when the end of the list is reached (failure).
 *
 * Two pruning rules are applied before branching:
 * 
 * 1. If the union of the currently covered points and all remaining candidates (precomputed in `suffix[idx]`) does not equal the full set, a complete cover is impossible.
 * 
 * 2. If the number of already chosen lines plus the remaining lines is less than the required 10 lines, a cover cannot be formed (exact cover by exactly
 *    10 lines is needed because each line covers exactly 10 points and there are 100 points total).
 *
 * Because every candidate line covers exactly `order` (10) points, any disjoint selection whose union reaches 100 points automatically contains exactly 10
 * lines and forms a partition; no additional bookkeeping for "used lines" is necessary beyond the overlap check `(m & covered) == 0`.
 *
 * @param B_indices Array of indices into the global candidate mask table `cand_masks_B` that defines the set of lines to search over.
 * @param B_count   Total number of entries in `B_indices`.
 * @param covered   Bitmask of grid points already covered by lines chosen in earlier recursive calls.
 * @param idx       Current position in the `B_indices` array (the next candidate to consider).
 * @param chosen    Number of lines selected so far on the current path.
 * @param suffix    Precomputed array where `suffix[i]` is the bitwise OR of the masks of all candidates from index `i` to `B_count-1`.
 *                  `suffix` must have length at least `B_count + 1`, with `suffix[B_count] == 0`.
 * @param path      Scratch buffer (length >= order) holding the `cand_masks_B` indices chosen so far on this path.
 * @param found     Output: one entry is appended (a copy of `path[0..order-1]`) for every complete exact cover discovered.
 *                  Only touched on successful leaves, so it adds no overhead to the pruning/branching hot path.
 */
static void count_exact_covers(const int B_indices[], int B_count,
							  __uint128_t covered, int idx, int chosen,
							  const __uint128_t suffix[],
							  int path[], vector<array<int, order>>& found) {
	if (covered == all_points_mask) {
		array<int, order> cover;
		for (int i = 0; i < order; ++i) cover[i] = path[i];
		found.push_back(cover);
		return;
	}
	if (idx >= B_count) return;

	// Prune 1: remaining lines cannot cover all points
	if ((covered | suffix[idx]) != all_points_mask) return;

	// Prune 2: not enough lines left to reach 10
	if (chosen + (B_count - idx) < 10) return;

	// Option 1: skip line idx
	count_exact_covers(B_indices, B_count, covered, idx + 1, chosen, suffix, path, found);

	// Option 2: include line idx if it doesn't overlap
	__uint128_t m = cand_masks_B[B_indices[idx]];
	if ((m & covered) == 0) {
		path[chosen] = B_indices[idx];
		count_exact_covers(B_indices, B_count, covered | m, idx + 1, chosen + 1, suffix, path, found);
	}
}

int get_refinements(const int B_indices[], const int& B_count, const __uint128_t union_B, vector<array<int, order>>& found) {
#if TRACK_TIME == 1
	auto timer = chrono::steady_clock::now();
#endif
	if (union_B != all_points_mask) {
		#if TRACK_TIME == 1
		total_refinement_early_blocking += chrono::duration<double>(chrono::steady_clock::now() - timer).count();
		#endif
		return -1;
	}

	if (B_count == order) {
		// Exactly `order` candidates and their union already covers every point (checked above),
		// so they must be pairwise disjoint -- this is the one and only refinement.
		array<int, order> cover;
		for (int i = 0; i < order; ++i) cover[i] = B_indices[i];
		found.push_back(cover);
		return 1;
	}

	__uint128_t suffix[B_count + 1];
	suffix[B_count] = 0;
	for (int i = B_count - 1; i >= 0; --i)
		suffix[i] = suffix[i + 1] | cand_masks_B[B_indices[i]];

	int path[order];
	count_exact_covers(B_indices, B_count, 0, 0, 0, suffix, path, found);
	int sol_count = (int)found.size();

#if TRACK_TIME == 1
	total_refinement_solve_time += chrono::duration<double>(chrono::steady_clock::now() - timer).count();
#endif

	return sol_count;
}

int processLine(const int sym_A_idx[order], vector<array<int, order>>& found) {
	++partial_count;

	#if TRACK_TIME == 1
	auto intersection_time = chrono::steady_clock::now();
	#endif
	int intersection_B_count = 0;
	__uint128_t union_B = 0;
	getIntersectingBLineIndices(intersecting_B_buf, intersection_B_count, sym_A_idx, union_B);
	#if TRACK_TIME == 1
	total_line_intersection_time += chrono::duration<double>(chrono::steady_clock::now() - intersection_time).count();
	#endif

	if (intersection_B_count < order)
		return -1;

	return get_refinements(intersecting_B_buf, intersection_B_count, union_B, found);
}

bool check_partial_solution_covering(const int sym_A_idx[order], __uint128_t& union_B) {
	#if TRACK_TIME == 1
	auto intersection_time = chrono::steady_clock::now();
	#endif

	getIntersectingBCovering(sym_A_idx, union_B);

	#if TRACK_TIME == 1
	double elapsed_3 = chrono::duration<double>(chrono::steady_clock::now() - intersection_time).count();
	total_line_covering_time += elapsed_3;
	#endif

	return union_B == all_points_mask;
}

bool solve_partial_solution(const int sym_A_idx[order]) {
	static thread_local vector<array<int, order>> found_B_refinements;
	found_B_refinements.clear();

	long int refinement_count = processLine(sym_A_idx, found_B_refinements);
	if (!g_test_mode)
		if (refinement_count > 0) {
			total_refinements += refinement_count;
#if WRITE_REFINEMENTS == 1
			write_separator(outfile);
			// Write all 10 A lines compactly
			for (int i = 0; i < order; ++i)
				write_compact_line(outfile, cand_masks_A[sym_A_idx[i]]);

			// Write every B-cover (10 lines each)
			for (const auto& cover : found_B_refinements)
				for (int i = 0; i < order; ++i)
					write_compact_line(outfile, cand_masks_B[cover[i]]);
#endif
			return false;
		} else if (refinement_count < 0)
			skipped_partial_solutions += 1;
	return true;
}

int setup(const vector<vector<vector<int>>> tmpl, string path, string ID) {
	output_path = path;
#if WRITE_REFINEMENTS == 1
	outfile.exceptions(std::ios::failbit | std::ios::badbit);
	outfile.open(output_path + "/solutions_" + ID + ".bin", std::ios::binary | std::ios::out);
	if (!outfile) {
		std::cerr << "Cannot open 'solutions_" + ID + ".bin' for writing\n";
		return 1;
	}
#endif

	ios::sync_with_stdio(false);
	cin.tie(nullptr);

	cout << "	Finding candidate lines from template..." << endl;
	find_candidate_lines(tmpl, true);
	find_candidate_lines(tmpl, false);
	
#if TRACK_TIME == 1
	candidate_find_time = chrono::duration<double>(chrono::steady_clock::now() - start_time).count();
#endif
	
	cout << "Precomputing all data structures..." << endl;
	precomputeDataStructures();
	
#if TRACK_TIME == 1
	precompute_time = chrono::duration<double>(chrono::steady_clock::now() - start_time).count() - candidate_find_time;
#endif
	return 0;
}

void print_substep_timings_log(double creation_time,
		double total_minimize_setup, double total_minimize_remove,
		double total_cube_gen_time, double total_cube_creation_time, double total_cube_solve_time) {
	double elapsed = chrono::duration<double>(chrono::steady_clock::now() - start_time).count(); 

	outfile.close();

	cout << "\n======= SUBSTEP DEFINITION  =======\n";
	cout << "When a partial solution is found in the SAT instance, we attempt to refine it into all its possible full solutions.\n";
#if EARLY == 1
	cout << "While looking for partial solutions, if they are incomplete, we check if they can extend to a full solution and block early if they cannot.\n";
#endif
	cout << "Each partial solution goes through a filter to process its compatible candidate lines, after which, these lines are checked to see if a solution is possible; skipping impossible partial solutions.\n";
	cout << "The filtered candidate lines then used in a custom algorithm to count all their possible refinements.\n";
#if MINIMIZE == 1
	cout << "Early blocking clauses and blocking clauses of partial solutions with no refinements are minimized to keep their clauses short.\n";
#endif

#if TRACK_TIME == 1
	double input_total = candidate_find_time + precompute_time;
	double refinement_total = total_refinement_early_blocking + total_refinement_solve_time;
	double line_total =  total_line_intersection_time + total_line_covering_time;
	double substep_total = line_total + refinement_total + input_total;

	double minimize_total = total_minimize_setup + total_minimize_remove;
	double post_processing = minimize_total;
	
	double sat_internal = total_cube_solve_time - (minimize_total + substep_total);
	double cubing_total = total_cube_gen_time + total_cube_creation_time + sat_internal;
	
	double accounted = creation_time + cubing_total + substep_total + post_processing;
	double other = elapsed - accounted;

	cout << "\n=== WALL TIMINGS ===\n";
	cout << "   Cube (SAT -> Solving + Early -> Minimize) -> Substep (INPUT -> FILTER -> REFINEMENT)\n";
	
	cout << "Cube:\n";
	cout << "   Generation: " << total_cube_gen_time << "s\n"; // march_cu
	cout << "   Solver Creation: " << total_cube_creation_time << "s\n";
	cout << "   Solving: " << total_cube_solve_time - substep_total << "s\n"; // cadical
	cout << "   Total: " << cubing_total << "s (Not including overlapping time)\n";

	cout << "SAT:\n";
	cout << "   Partial solutions processed: " << partial_count << " (" << skipped_partial_solutions << " skipped)\n";
	cout << "   Throughput: " << (partial_count / elapsed) << " partial solutions/sec\n";
	cout << "   Processed Throughput: " << ((partial_count - skipped_partial_solutions) / elapsed) << " extendable partial solutions/sec\n";
	cout << "   Creation time: " << creation_time << "s\n";
	cout << "   Internal time: " << sat_internal << "s\n";
	cout << "   Total: " << sat_internal + creation_time << "s (Remaining Time)\n";
	#if MINIMIZE == 1
	cout << "Minimize:\n";
	cout << "   Setup Minimization: " << total_minimize_setup << "s\n";
	cout << "   Remove Redundant Lines: " << total_minimize_remove << "s\n";
	cout << "   Total: " << minimize_total << "s\n";
	#endif
	cout << "\nInput:\n";
	cout << "   Finding Candidate Lines took: " << candidate_find_time << "s\n";
	cout << "   Precomputing the required datastructures took: " << precompute_time << "s\n";
	cout << "   Total: " << input_total << "s\n";

	cout << "Filter:\n";
	cout << "   Check Covering Valid Intersecting Lines: " << total_line_covering_time << "s\n";
	cout << "   Keep Valid Intersecting Lines: " << total_line_intersection_time << "s\n";
	cout << "   Total: " << line_total << "s\n";

	cout << "Refinement:\n";
	cout << "   Creation: " << total_refinement_early_blocking << "s (early covering check)\n";
	cout << "   Solving: " << total_refinement_solve_time << "s\n";
	cout << "   Total: " << refinement_total << "s\n";
	
	cout << "Substep Total: " << line_total + refinement_total + input_total << "s\n";
	cout << "Total: " << elapsed << "s\n";
	cout << "Other/Extra: " << other << "s\n";
#endif
}