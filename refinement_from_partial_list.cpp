#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <unordered_set>
#include <string>
#include <tuple>
#include <chrono>
#include <algorithm>

#include <cstdlib>

#include "cadical.hpp"
#include "exhaustive.hpp"

#ifdef _OPENMP
#define ENABLE_MT 1
#include <omp.h>
#include <atomic>
#else
#define ENABLE_MT 0
#endif

#define TRACK_TIME 1
#define PRINT_TIME 0
#define MAX_RUNTIME 30 // a value below or equal to 0 skips timeout

using namespace std;

// Global data structures
const int order = 10;

const vector<int> observed;

unordered_set<int> points_A;
unordered_set<int> points_B;
unordered_set<int> total_points;

uint64_t* intersects_once_AB = nullptr; // bitset table intersects_once_AB[j * rows_A + w]: bit i set iff intersections_AB[i*count_B+j] == 1
uint64_t* intersects_once_BA = nullptr;
int rows_A = 0; // ceil(count_A / 64)
int rows_B = 0;
int* all_line_indices_A = nullptr;
int* all_line_indices_B = nullptr;

long skipped_partial_solutions = 0;
long partial_count = 0;
int count_A = 0;
int count_B = 0;

uint64_t* overlaps_AA = nullptr;
uint64_t* overlaps_BB = nullptr;

__uint128_t all_points_mask; // bit (p-1) set means point p is on this line (points 1–100, so bits 0–99 used)

vector<__uint128_t> cand_masks_A; 
vector<__uint128_t> cand_masks_B;

#if TRACK_TIME == 1 // This tracking probably doesn't work the best when we are multithreading, TODO: fix that
double total_sat_solving_time = 0.0; // wall time
double total_sat_atmost1_time = 0.0;
double total_sat_atleast1_time = 0.0;
double total_sat_intersection_time = 0.0;
double total_sat_setup_time = 0.0;

double total_line_read_time = 0.0;
double total_line_finding_time = 0.0;
double total_line_parallel_time = 0.0;
double total_line_intersection_time = 0.0;
#endif

struct U128Hash {
    size_t operator()(__uint128_t v) const {
        uint64_t lo = (uint64_t)v;
        uint64_t hi = (uint64_t)(v >> 64);
        size_t h = lo;
        h ^= hi + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
        return h;
    }
};

unordered_map<__uint128_t, int, U128Hash> cand_hash_A;
unordered_map<__uint128_t, int, U128Hash> cand_hash_B;

// Debugging helpers (not used in hot path)
void mask_print(__uint128_t m) {
    uint64_t hi = (uint64_t)(m >> 64);
    uint64_t lo = (uint64_t)m;
    for (int i = 63; i >= 0; --i) {
        cout << ((hi >> i) & 1);
        if (i % 8 == 0 && i > 0) cout << " ";
    }
    for (int i = 63; i >= 0; --i) {
        cout << ((lo >> i) & 1);
        if (i % 8 == 0 && i > 0) cout << " ";
    }
    cout << endl;
}

bool mask_isSet(__uint128_t m, int p) {
    if (p < 0 || p > 127) return false;
    return (m >> p) & 1;
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
 * @brief Constructs a 128-bit __uint128_t from a fixed-length array of point indices (only 100 bits are used).
 * @param line A raw array of exactly `order` point values in the range [1, 100]. Each value is converted to a 0-based bit index and set in the __uint128_t.
 * @returns A __uint128_t with bits set at each position corresponding to a point in line.
 */
__uint128_t make_mask(const int* line) {
    __uint128_t m = 0;
    for (int i = 0; i < order; i++)
        m |= ((__uint128_t)1 << (line[i] - 1)); // convert 1-100 to bit index 0-99
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
 * @brief Checks if two Masks intersect.
 * Uses bitwise operators on both halves of the masks to check if they intersect.
 * @param m1 The first __uint128_t.
 * @param m2 The second __uint128_t.
 * @returns If m1 and m2 intersect.
 */
bool linesIntersect(__uint128_t m1, __uint128_t m2) {
    return (m1 & m2) != 0;
}

/**
 * @brief Parses a space-separated list of integers from a prefixed text line.
 * Returns an empty vector if the line is empty or does not begin with the expected prefix character. The prefix and the character immediately after it (assumed to be a space) are stripped before parsing.
 * @param line   The raw text line to parse.
 * @param prefix The expected first character of the line ('R' or 'N').
 * @returns A vector of integers parsed from the remainder of the line, or an empty vector if the line does not match the prefix.
 */
vector<int> parse_line(const string& line, char prefix) {
	vector<int> result;
	if (line.empty() || line[0] != prefix) 
		return result;
	istringstream iss(line.substr(2));
	int val;
	while (iss >> val) 
		result.push_back(val);
	return result;
}

/**
 * @brief Loads candidate lines from a text file and converts them to Masks.
 * Each line in the file beginning with 'R' or 'N' is parsed as a list of point indices and converted to a __uint128_t. All points encountered across all lines are collected into a set.
 * @param path Path to the candidate lines file.
 * @returns A tuple of: the vector of Masks, the set of all points seen, and the total number of lines loaded.
 */
tuple<vector<__uint128_t>, unordered_set<int>, int> load_candidate_lines_file(const string& path) {
	ifstream f(path);
	vector<__uint128_t> lines;
	unordered_set<int> points;
	string line;
	while (getline(f, line)) {
		if (line.empty()) continue;
		char prefix = line[0];
		if (prefix == 'R' || prefix == 'N') {
			vector<int> nums = parse_line(line, prefix);
			if (!nums.empty()) {
				lines.push_back(make_mask(nums));
				for (int p : nums) 
					points.insert(p);
			}
		}
	}
	return {lines, points, (int)lines.size()};
}

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
 * @brief Converts a (row, col) grid position to a 1-based flat point index.
 * Points are numbered left-to-right, top-to-bottom starting from 1, matching the convention used in the candidate lines files.
 * @param r 0-based row index.
 * @param c 0-based column index.
 * @returns The 1-based point index at position (r, c).
 */
int get1DIndex(int r, int c) {
	return r * order + c + 1;
}

/**
 * @brief Extracts the symbol-lines from a partial SAT solution for both squares.
 * A symbol-line is the set of `order` grid points assigned to a single symbol within one square. 
 * For each symbol in each square, if all `order` assignments are present in the solution, the corresponding line is added as a __uint128_t, otherwise line is skipped.
 * @param solution        Array of positive SAT literals representing the solution.
 * @param solution_count  Number of literals in the solution array.
 * @param a_lines         Output array to write Masks for square A lines into.
 * @param a_solutions     Running count of lines written to a_lines (modified in place).
 * @param b_lines         Output array to write Masks for square B lines into.
 * @param b_solutions     Running count of lines written to b_lines (modified in place).
 */
void solutionToCandidateLines(const int* solution, const int& solution_count, __uint128_t a_lines[], int& a_solutions, __uint128_t b_lines[], int& b_solutions) {
    int points_by_symbol[2][order][order];
    int counts[2][order] = {0};

	for(int i = 0; i < solution_count; i++) {
		int var = solution[i];
		if (var <= 0) continue;
		auto [sq, r, c, s] = indexTo4Tuple(var, 2, order, order, order);
		int point = get1DIndex(r, c);
        int &cnt = counts[sq][s];
        if (cnt < order) {
            points_by_symbol[sq][s][cnt++] = point;
        }
	}

	for (int sq = 0; sq < 2; ++sq)
		for (int s = 0; s < order; ++s)
            if (counts[sq][s] == order) {
				if (sq == 0) 
					a_lines[a_solutions++] = make_mask(points_by_symbol[sq][s]);
				else 
					b_lines[b_solutions++] = make_mask(points_by_symbol[sq][s]);
			}
}

/**
 * @brief Precomputes all data structures needed for fast per-solution filtering and SAT encoding.
 *
 * Builds four bitset tables, all in flat row-major layout where each row is a bitset over the lines of one square packed into 64-bit words:
 *
 *  - `intersects_once_AB[j * rows_A + w]`: bit i set iff A line i intersects B line j exactly once,
 *
 *  - `intersects_once_BA[i * rows_B + w]`: bit j set iff B line j intersects A line i exactly once
 *    (both transposes of each other, allows us row-major access from either direction).
 *
 *  - `overlaps_AA[i * rows_A + w]`: bit j set iff A lines i and j share at least one point
 *    (Symmetric: `overlaps_AA[i]` has bit j set iff `overlaps_AA[j]` has bit i set),
 *
 *  - `overlaps_BB[i * rows_B + w]`: same as overlaps_AA but for square B lines.
 *
 * With ~14k lines per side, intersects_once_AB/BA are ~24MB each and overlaps_AA/BB are ~24MB each. 
 * All four fit in L3 cache, keeping the bit lookups fast across all tens of millions of calls.
 *
 * Also initialises:
 * 
 *  - `all_line_indices_A/B`: identity index arrays [0, 1, ..., count-1] used as the default candidate set when no filtering has been applied.
 * 
 *  - `cand_hash_A/B`: __uint128_t-to-index lookup maps for resolving solution lines to their global candidate indices.
 */
void precomputeDataStructures() {
    auto start = chrono::steady_clock::now();

	all_points_mask = ((__uint128_t)1 << 100) - 1; // bits 0–99 set, one per grid point
    
    rows_A = (count_A + 63) / 64;
    rows_B = (count_B + 63) / 64;
    intersects_once_AB = new uint64_t[(long long)count_B * rows_A](); // intersects_once_AB[j * rows_A + w]: bit i set iff A line i intersects B line j exactly once.
    intersects_once_BA = new uint64_t[(long long)count_A * rows_B]();

    for (int i = 0; i < count_A; ++i) 
        for (int j = 0; j < count_B; ++j) { // for every (A line i, B line j) pair, compute how many points they share
            if (intersectsExactlyOnce(cand_masks_A[i], cand_masks_B[j])) {
				// store pair as bit in row j of intersects_once_AB. Each row is `rows_A` 64-bit words wide, so row j starts at offset j*rows_A
				// line i defined in word i/64 of that row, at bit position i%64. Setting that bit says: A line i intersects B line j exactly once
                intersects_once_AB[(long long)j * rows_A + i / 64] |= (1ULL << (i % 64));
                intersects_once_BA[(long long)i * rows_B + j / 64] |= (1ULL << (j % 64)); // symmetric entry, row i, word j/64, bit j%64
            }
        }
	
	// zero-initialized bitset table: count_A rows, each rows_A is words wide
    overlaps_AA = new uint64_t[(long long)count_A * rows_A](); // overlaps_AA[i * rows_A + j/64] bit (j%64) will be set iff A lines i and j share >= 1 point.
    for (int i = 0; i < count_A; i++)
        for (int j = i + 1; j < count_A; j++) // j > i: fill upper triangle only, then mirror to avoid redundant work
            if (linesIntersect(cand_masks_A[i], cand_masks_A[j])) {
                overlaps_AA[(long long)i * rows_A + j / 64] |= (1ULL << (j % 64)); // Row i, word j/64, bit j%64 marks that line j overlaps line i
                overlaps_AA[(long long)j * rows_A + i / 64] |= (1ULL << (i % 64)); // (symmetric) Row j, word i/64, bit i%64 marks that line i overlaps line j
            }
 
    overlaps_BB = new uint64_t[(long long)count_B * rows_B](); // same as overlaps_AA but for Bs
    for (int i = 0; i < count_B; i++)
        for (int j = i + 1; j < count_B; j++)
            if (linesIntersect(cand_masks_B[i], cand_masks_B[j])) {
                overlaps_BB[(long long)i * rows_B + j / 64] |= (1ULL << (j % 64));
                overlaps_BB[(long long)j * rows_B + i / 64] |= (1ULL << (i % 64));
            }

	all_line_indices_A = new int[count_A];
	for(int i = 0; i < count_A; i++)
		all_line_indices_A[i] = i;
	all_line_indices_B = new int[count_B];
	for(int i = 0; i < count_B; i++)
		all_line_indices_B[i] = i;

	cand_hash_A.reserve(count_A);
	for (int i = 0; i < count_A; ++i)
		cand_hash_A[cand_masks_A[i]] = i;
	cand_hash_B.reserve(count_B);
	for (int i = 0; i < count_B; ++i)
		cand_hash_B[cand_masks_B[i]] = i;

    auto end = chrono::steady_clock::now();
    double elapsed = chrono::duration<double>(end - start).count();
    cout << "Precomputed intersections using masks in " << elapsed << " seconds." << endl;
    //cout << "  A-B: " << cand_lines_A.size() << "x" << cand_lines_B.size() << " = " << (cand_lines_A.size() * cand_lines_B.size()) << " entries" << endl;
}

/**
 * @brief Finds all candidate lines that share no points with a given set of lines.
 *
 * Parallel means having zero intersection with every line in the input set, i.e. the candidate occupies a completely disjoint set of points. The solution lines themselves are always included in the output regardless.
 *
 * Special cases:
 * 
 *   - If line_count == 0, returns the full candidate list (no constraint).
 * 
 *   - If line_count == order, the solution is complete; only the solution lines themselves are returned (nothing can be parallel to a full covering).
 *
 * @param parallel_indices  Output array to write the result indices into. Must be pre-allocated to at least count_A or count_B.
 * @param parallel_count    Running count of indices written (modified in place).
 * @param line_indices      Indices of the solution lines (prepended to output unconditionally).
 * @param line_count        Number of solution lines provided.
 * @param total_incidence   Pre-computed union mask of all solution line masks. Avoids redundant mask[index] lookups
 *                          since the caller already holds the raw masks before the hash lookup.
 * @param is_A              If true, operates on square A candidates; otherwise square B.
 */
void getAllParallelLineIndices(int*& parallel_indices, int& parallel_count, const int line_indices[], const int line_count, const __uint128_t& total_incidence, bool is_A) {
    int*        all      = is_A ? all_line_indices_A  : all_line_indices_B;
    const int   all_size = is_A ? count_A             : count_B;
    const auto& masks    = is_A ? cand_masks_A        : cand_masks_B;

    if (line_count == 0) {
        parallel_indices = all;
        parallel_count   = all_size;
        return;
    }

    for(int i = 0; i < line_count; i++)
        parallel_indices[parallel_count++] = line_indices[i];

    if (line_count == order)
        return;

    for (size_t i = 0; i < masks.size(); i++)
        if(!linesIntersect(masks[i], total_incidence))
            parallel_indices[parallel_count++] = i;
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
 * @param line_indices         Candidate line indices to test (e.g. from getAllParallelLineIndices).
 * @param line_count           Number of candidate lines to test.
 * @param opposite_indices     Indices of the opposite square's solution lines.
 * @param opposite_count       Number of opposite solution lines.
 * @param is_A                 If true, line_indices are A lines tested against B opposites; otherwise B lines tested against A opposites.
 */
void getIntersectingLineIndices(int intersecting_indices[], int& intersection_count, const int line_indices[], const int line_count, const int opposite_indices[], const int opposite_count, bool is_A) {
    const int    words       	 = is_A ? rows_A 			 : rows_B;
    const uint64_t* bitset_table = is_A ? intersects_once_AB : intersects_once_BA;

    uint64_t* result = (uint64_t*)alloca(words * sizeof(uint64_t));

    if (opposite_count == 0)
        memset(result, 0xFF, words * sizeof(uint64_t));
    else {
        memcpy(result, bitset_table + (long long)opposite_indices[0] * words, words * sizeof(uint64_t));
        for (int j = 1; j < opposite_count; j++) {
            const uint64_t* row = bitset_table + (long long)opposite_indices[j] * words;
            for (int w = 0; w < words; w++)
                result[w] &= row[w];
        }
    }

    for (int i = 0; i < line_count; i++) {
        const int idx = line_indices[i];
        if ((result[idx / 64] >> (idx % 64)) & 1)
            intersecting_indices[intersection_count++] = idx;
    }
}

/**
 * @brief Counts valid refinements using exhaustive SAT solving.
 *
 * Encodes the candidate lines for both squares as a SAT problem and uses an exhaustive search propagator to count all satisfying assignments. Each
 * solution corresponds to a pair of complete transversals (one from square A, one from square B) that together form a valid refinement.
 *
 * The SAT encoding imposes three constraints:
 * 
 *   1. Covering: every grid point must be covered by at least one chosen line in each square (unit clauses per point).
 * 
 *   2. Non-overlap: no two chosen lines within the same square may share a point (pairwise exclusion clauses, skipped when the square is already fully determined by the solution).
 *
 *   3. Cross-intersection: each chosen A line must intersect each chosen B line exactly once (pairwise exclusion clauses for non-unit intersections).
 *
 * @param trans_A   Number of A lines already determined by the partial solution.
 * @param trans_B   Number of B lines already determined by the partial solution.
 * @param A_indices Candidate A line indices that passed parallel + intersection filtering.
 * @param A_count   Number of candidate A lines.
 * @param B_indices Candidate B line indices that passed parallel + intersection filtering.
 * @param B_count   Number of candidate B lines.
 * @returns The total number of valid refinements found.
 */
int get_refinements(const int& trans_A, const int& trans_B, const int A_indices[], const int A_count, const int B_indices[], const int B_count) {
#if TRACK_TIME == 1
    auto timer = chrono::steady_clock::now();
#endif
    
    CaDiCaL::Solver solver;
	//solver.resize(A_count + B_count); // experimental: for 3.0

	if (trans_A < order)
	{
		__uint128_t total_incidence_A = cand_masks_A[A_indices[0]];
		for(int i=1; i < A_count; i++) // get all points contained in line indices
			total_incidence_A |= cand_masks_A[A_indices[i]];
		if(total_incidence_A != all_points_mask) // return immedately if not covering all points
			return -1;
	}

	if (trans_B < order)
	{
		__uint128_t total_incidence_B = cand_masks_B[B_indices[0]];
		for(int i=1; i < B_count; i++)
			total_incidence_B |= cand_masks_B[B_indices[i]];
		if(total_incidence_B != all_points_mask)
			return -1;
	}

	for(int i = 0; i < trans_A; i++)
		solver.clause(i+1);
	for(int i = 0; i < trans_B; i++)
		solver.clause(i+1+A_count);

#if TRACK_TIME == 1
    double setup_elapsed = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	timer = chrono::steady_clock::now();
#endif

    if (trans_A < order) // if A is not fully determined by the partial solution
        for (int i = 0; i < A_count; i++)
            for (int j = i + 1; j < A_count; j++) // check if lines A_indices[i] and A_indices[j] overlap
				// row A_indices[i], word A_indices[j]/64 gives the right 64-bit word, right-shifting by A_indices[j]%64 moves the target bit to position 0.
                if ((overlaps_AA[(long long)A_indices[i] * rows_A + A_indices[j] / 64] >> (A_indices[j] % 64)) & 1) // AND with 1 isolates bit: result is 1 if they overlap, 0 if not.
                    solver.clause(-(i + 1), -(j + 1)); // at most one of SAT var i+1, var j+1 may be chosen
 
    if (trans_B < order)
        for (int i = 0; i < B_count; i++)
            for (int j = i + 1; j < B_count; j++)
                if ((overlaps_BB[(long long)B_indices[i] * rows_B + B_indices[j] / 64] >> (B_indices[j] % 64)) & 1)
                    solver.clause(-(i + 1 + A_count), -(j + 1 + A_count));

#if TRACK_TIME == 1
    double atmost_elapsed = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	timer = chrono::steady_clock::now();
#endif

    {
		// stack-allocated flat buffer of (point, var) pairs: one entry per set bit across all filtered candidates.
        int* buf_point = (int*)alloca(A_count * order * sizeof(int));
        int* buf_var   = (int*)alloca(A_count * order * sizeof(int));
        int  buf_len   = 0;
 
        for (int i = 0; i < A_count; i++) {
            const int var = i + 1; // SAT variable for this candidate (1-based)
            uint64_t lo = (uint64_t)cand_masks_A[A_indices[i]];        // bits 0–63: grid points 0–63
            uint64_t hi = (uint64_t)(cand_masks_A[A_indices[i]] >> 64); // bits 0–35: grid points 64–99
            while (lo) { 
				int b = __builtin_ctzll(lo); // count trailing zeros = index of the lowest set bit = covered point index
				buf_point[buf_len] = b; 	 // record which point this candidate covers
				buf_var[buf_len++] = var;	 // record which SAT var covers it
				lo &= lo - 1; // clear the lowest set bit: lo-1 flips all bits up to and including it, ANDing with lo zeroes that bit and leaves all higher bits unchanged
			}
            while (hi) { 
				int b = __builtin_ctzll(hi); 
				buf_point[buf_len] = 64 + b; // add 64 because hi bits represent points 64–99
				buf_var[buf_len++] = var; 
				hi &= hi - 1; 
			}
        }
 
        // counting sort by point index (range [0, order^2)) so we can group vars by point they cover and add one covering clause per point
		int cnt[order * order] = {};
        for (int k = 0; k < buf_len; k++) 
			cnt[buf_point[k]]++; // tally how many vars cover each point
        int off[order * order + 1];
        off[0] = 0;
        for (int p = 0; p < order * order; p++) 
			off[p + 1] = off[p] + cnt[p]; // exclusive prefix sum
		// off[p] = start index in sorted_vars for point p, off[p+1] = start index for point p+1, so sorted_vars[off[p]..off[p+1]) is the slice for point p
 
        int* sorted_vars = (int*)alloca(buf_len * sizeof(int));
        memset(cnt, 0, sizeof(cnt)); // reuse cnt as a per-point write cursor into sorted_vars
        for (int k = 0; k < buf_len; k++) {
            int p = buf_point[k];
            sorted_vars[off[p] + cnt[p]++] = buf_var[k]; // off[p] is the base for point p's slice;
				// cnt[p] is how many vars have been written there so far, so off[p]+cnt[p] is the next empty slot; then cnt[p] is incremented
        }
 
        for (int p = 0; p < order * order; p++) {
            for (int k = off[p]; k < off[p + 1]; k++) 
				solver.add(sorted_vars[k]); // add each var that covers point p as a literal in this clause
            solver.add(0); // terminate clause with 0: encodes at least one of these vars must be true
        }
    }
 
    { // Same for B.
        int* buf_point = (int*)alloca(B_count * order * sizeof(int));
        int* buf_var   = (int*)alloca(B_count * order * sizeof(int));
        int  buf_len   = 0;
 
        for (int i = 0; i < B_count; i++) {
            const int var = i + 1 + A_count;
            uint64_t lo = (uint64_t)cand_masks_B[B_indices[i]];
            uint64_t hi = (uint64_t)(cand_masks_B[B_indices[i]] >> 64);
            while (lo) { 
				int b = __builtin_ctzll(lo); 
				buf_point[buf_len] = b;      
				buf_var[buf_len++] = var; 
				lo &= lo - 1; 
			}
            while (hi) { 
				int b = __builtin_ctzll(hi); 
				buf_point[buf_len] = 64 + b; 
				buf_var[buf_len++] = var; 
				hi &= hi - 1; 
			}
        }
 
        int cnt[order * order] = {};
        for (int k = 0; k < buf_len; k++) 
			cnt[buf_point[k]]++;
        int off[order * order + 1];
        off[0] = 0;
        for (int p = 0; p < order * order; p++) 
			off[p + 1] = off[p] + cnt[p];
 
        int* sorted_vars = (int*)alloca(buf_len * sizeof(int));
        memset(cnt, 0, sizeof(cnt));
        for (int k = 0; k < buf_len; k++) {
            int p = buf_point[k];
            sorted_vars[off[p] + cnt[p]++] = buf_var[k];
        }
 
        for (int p = 0; p < order * order; p++) {
            for (int k = off[p]; k < off[p + 1]; k++) 
				solver.add(sorted_vars[k]);
            solver.add(0);
        }
    }

#if TRACK_TIME == 1
    double atleast_elapsed = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	timer = chrono::steady_clock::now();
#endif

    if(trans_A > 0 && trans_B > 0) {
        for (size_t i = 0; i < A_count; i++) {
            const int a_idx = A_indices[i];
            const int a_var = i + 1;
        	for (size_t j = 0; j < B_count; j++) 
                if (!((intersects_once_AB[(long long)B_indices[j] * rows_A + a_idx / 64] >> (a_idx % 64)) & 1))
                    solver.clause(-a_var, -(A_count + j + 1));
        }
    }
    
#if TRACK_TIME == 1
    double intersections_elapsed = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	timer = chrono::steady_clock::now();
#endif

    ExhaustiveSearch propagator(&solver, observed, true, nullptr, false);	

    int result = solver.solve();
    long int sol_count = propagator.get_solution_count();
    
#if TRACK_TIME == 1
    double solver_elapsed = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	#if PRINT_TIME == 1
    cout << "Encoding took " << (setup_elapsed + covering_elapsed + intersections_elapsed) << "; Setup took " << setup_elapsed << ", Covering took " << covering_elapsed << ", and Intersections took " << intersections_elapsed
		<< ", Refinement search took " << solver_elapsed << " (Total: " << (setup_elapsed + covering_elapsed + intersections_elapsed + solver_elapsed) << ")\n";
	#endif
	total_sat_setup_time += setup_elapsed;
	total_sat_atleast1_time += atleast_elapsed;
	total_sat_atmost1_time += atmost_elapsed;
	total_sat_intersection_time += intersections_elapsed;
	total_sat_solving_time += solver_elapsed;
#endif

    return sol_count;
}

/**
 * @brief Processes a single partial solution line and counts its refinements.
 *
 * Parses the SAT literal string, extracts the symbol-lines determined by the partial solution, then runs a three-stage filtering pipeline to find
 * candidate lines for each square that could complete a valid refinement:
 * 
 *   1. solutionToCandidateLines: extract solution lines as Masks and look up their indices in the candidate hash maps.
 * 
 *   2. getAllParallelLineIndices: keep only candidates sharing no points with the same square's solution lines.
 * 
 *   3. getIntersectingLineIndices: keep only candidates intersecting each of the opposite square's solution lines exactly once.
 *
 * The surviving candidates are passed to get_refinements for SAT-based counting.
 *
 * @param line A space-separated string of non-zero SAT literals representing a partial solution. A trailing '0' is stripped if present.
 * @returns The number of valid refinements found for this partial solution, or 0 if the line is empty or yields no valid candidates.
 */
int processLine(string& line)
{
#if TRACK_TIME == 1
	auto read_time = chrono::steady_clock::now();
#endif 
	if (line.empty()) 
		return 0;
	if (line.back() == '0')
		line.pop_back();

	istringstream iss(line);
	int solution[order * order];
	int solution_count = 0;
	int x;
	while (iss >> x)
		if (x != 0) 
			solution[solution_count++] = x;

	#if ENABLE_MT == 1
	#pragma omp atomic
	++partial_count;
	#else
	++partial_count;
	#endif
	
#if TRACK_TIME == 1
	double elapsed_0 = chrono::duration<double>(chrono::steady_clock::now() - read_time).count();
	auto conversion_time = chrono::steady_clock::now();
#endif 

	__uint128_t A_sol_lines[order];
	int trans_A = 0;
	__uint128_t B_sol_lines[order];
	int trans_B = 0;

	solutionToCandidateLines(solution, solution_count, A_sol_lines, trans_A, B_sol_lines, trans_B);

#if TRACK_TIME == 1
	double elapsed_1 = chrono::duration<double>(chrono::steady_clock::now() - conversion_time).count();
	auto index_time = chrono::steady_clock::now();
#endif

	// Build total_incidence directly from raw solution masks
	__uint128_t total_incidence_A = 0;
	__uint128_t total_incidence_B = 0;
	
	// Convert solution lines to their candidate line indices and compute incidence strings
	int A_sol_indices[trans_A];
	int B_sol_indices[trans_B];
	for (int i = 0; i < trans_A; i++) {
		A_sol_indices[i] = cand_hash_A[A_sol_lines[i]];
		total_incidence_A |= A_sol_lines[i];
	}
	for (int i = 0; i < trans_B; i++) {
		B_sol_indices[i] = cand_hash_B[B_sol_lines[i]];
		total_incidence_B |= B_sol_lines[i];
	}

#if TRACK_TIME == 1
	double elapsed_index = chrono::duration<double>(chrono::steady_clock::now() - index_time).count();
	auto parallel_time = chrono::steady_clock::now();
#endif

	int* parallel_A_indices = (int*)alloca(count_A * sizeof(int));
	int  parallel_A_count = 0;
	int* parallel_B_indices = (int*)alloca(count_B * sizeof(int));
	int  parallel_B_count = 0;

	getAllParallelLineIndices(parallel_A_indices, parallel_A_count, A_sol_indices, trans_A, total_incidence_A, true);
	getAllParallelLineIndices(parallel_B_indices, parallel_B_count, B_sol_indices, trans_B, total_incidence_B, false);

#if TRACK_TIME == 1
	double elapsed_2 = chrono::duration<double>(chrono::steady_clock::now() - parallel_time).count();
	auto intersection_time = chrono::steady_clock::now();
#endif

	// Filter to those that intersect exactly once with every line of the opposite square's solution using precomputed intersections
	int intersecting_A_indices[parallel_A_count];
	int intersection_A_count = 0;
	int intersecting_B_indices[parallel_B_count];
	int intersection_B_count = 0;

	getIntersectingLineIndices(intersecting_A_indices, intersection_A_count, parallel_A_indices, parallel_A_count, B_sol_indices, trans_B, true);
	getIntersectingLineIndices(intersecting_B_indices, intersection_B_count, parallel_B_indices, parallel_B_count, A_sol_indices, trans_A, false);

#if TRACK_TIME == 1
	double elapsed_3 = chrono::duration<double>(chrono::steady_clock::now() - intersection_time).count();
	#if PRINT_TIME == 1
	cout << "Conversion Time: " << elapsed_1 << ", Index Finding: " << elapsed_index << ", Parallel Time: " << elapsed_2 << ", Intersection Time: " << elapsed_3 << " (Total: " << (elapsed_1 + elapsed_index + elapsed_2 + elapsed_3) << ")" << endl;
	#endif
	total_line_read_time += elapsed_0 + elapsed_1;
	total_line_finding_time += elapsed_index;
	total_line_parallel_time += elapsed_2;
	total_line_intersection_time += elapsed_3;
#endif

	long int refinement_count = get_refinements(trans_A, trans_B, intersecting_A_indices, intersection_A_count, intersecting_B_indices, intersection_B_count);

	return refinement_count;
}

// ------------------------------------------------------------
// Main
// ------------------------------------------------------------
int main(int argc, char* argv[]) {
	if (argc < 3) {
		cerr << "Usage: " << argv[0] << " <template_id> <file_name>\n";
		return 1;
	}

	int template_id = atoi(argv[1]) + 1;
	string solution_file = argv[2];
	
	auto start_time = chrono::steady_clock::now(); // Precompute masks
	cout << "Loading candidate lines from files..." << endl;

	string parent_dir = "../refinements and candidate lines/";
	string candidate_lines_2_path = parent_dir + "2-candidate_lines/" + to_string(template_id) + "-candidate_lines.txt";
	string candidate_lines_3_path = parent_dir + "3-candidate_lines/" + to_string(template_id) + "-candidate_lines.txt";

	tie(cand_masks_A, points_A, count_A) = load_candidate_lines_file(candidate_lines_2_path);
	tie(cand_masks_B, points_B, count_B) = load_candidate_lines_file(candidate_lines_3_path);

	total_points = points_A;
	total_points.insert(points_B.begin(), points_B.end());
	
	cout << "Load time: " << chrono::duration<double>(chrono::steady_clock::now() - start_time).count() << endl;
	
	cout << "Precomputing all data structures..." << endl;
	precomputeDataStructures();

	ifstream sol_stream(solution_file);
	if (!sol_stream) {
		cerr << "Cannot open solution file: " << solution_file << endl;
		return 1;
	}
	
	long long total_refinements = 0;

	unordered_set<string> seen;
	seen.reserve(1500000);
	
	start_time = chrono::steady_clock::now();
	#if ENABLE_MT == 0
		string line;
		while (getline(sol_stream, line))
			if (!line.empty())
				if (seen.insert(line).second) {
					long int refinement_count = processLine(line); 
					if(refinement_count > 0)
						total_refinements += refinement_count;
					else if(refinement_count < 0)
						skipped_partial_solutions += 1;
					if (partial_count % 1000 == 0) { 
						auto current_time = chrono::steady_clock::now();
						double elapsed = chrono::duration<double>(current_time - start_time).count();
						cout << "Processed " << partial_count << " partial solutions. Time elapsed: " << elapsed << " seconds with total refinements: " << total_refinements << endl;
					}
					if(MAX_RUNTIME > 0 && MAX_RUNTIME < chrono::duration<double>(chrono::steady_clock::now() - start_time).count())
						break;
				}
		sol_stream.close();
		cout << "\n";
	#else
		vector<string> all_solution_lines;
		all_solution_lines.reserve(1500000);
		
		string line;
		while (getline(sol_stream, line)) {
			if (!line.empty()) {
				if (seen.insert(line).second) 
					all_solution_lines.push_back(move(line));
			}
		}
		sol_stream.close();
		seen = unordered_set<string>();
		
		cout << "Loaded " << all_solution_lines.size() << " solutions to process.\n"; // show add a timer for this to display how long this took
		
		atomic<bool> abort_early(false);

		auto max_threads = omp_get_max_threads();
		int limit_threads = 2;
		int curr_threads = max(1, max_threads - limit_threads);

		omp_set_num_threads(curr_threads);
		
		start_time = chrono::steady_clock::now();
		#pragma omp parallel for schedule(dynamic)
		for (size_t sol_idx = 0; sol_idx < all_solution_lines.size(); sol_idx++)
			if (!abort_early) {
				string& line = all_solution_lines[sol_idx];
				long int refinement_count = processLine(line); 
				if (refinement_count > 0) {
					#pragma omp atomic
					total_refinements += refinement_count;
				}
				else if(refinement_count < 0) {
					#pragma omp atomic
					skipped_partial_solutions += 1;
				}
				if (partial_count % 1000 == 0) {
					#pragma omp critical(logging)
					{
						auto current_time = chrono::steady_clock::now();
						double elapsed = chrono::duration<double>(current_time - start_time).count();
						
						cout << "Processed " << partial_count << " partial solutions. Time elapsed: " << elapsed << " seconds with total refinements: " << total_refinements << endl;
					}
				}
				if(MAX_RUNTIME > 0 && MAX_RUNTIME < chrono::duration<double>(chrono::steady_clock::now() - start_time).count())
					abort_early = true;
			}
		cout << "\n(" << curr_threads << " THREADS)\n";
	#endif

	double elapsed = chrono::duration<double>(chrono::steady_clock::now() - start_time).count();
	
	cout << "=== FINAL RESULTS FOR TEMPLATE " << template_id - 1 << " ===\n";
	cout << "Total refinements found: " << total_refinements << endl;
	cout << "Partial solutions processed: " << partial_count << " (" << skipped_partial_solutions << " skipped)" << endl;
	cout << "Time elapsed: " << elapsed << " seconds\n";
	cout << "Throughput: " << (partial_count / elapsed) << " solutions/sec\n";
	cout << "File: " << solution_file << endl;

#if TRACK_TIME == 1
	double sat_total_encode = total_sat_atmost1_time + total_sat_atleast1_time + total_sat_intersection_time;
	double sat_total = sat_total_encode + total_sat_solving_time;
	double line_total = total_line_read_time + total_line_finding_time + total_line_parallel_time + total_line_intersection_time;

	cout << "\n=== TOTAL TIMES FOR THIS RUN ===\n";
	cout << "SAT Setup: " << total_sat_setup_time << "s" << endl;
	cout << "SAT At-Most: " << total_sat_atmost1_time << "s" << endl;
	cout << "SAT At-Least: " << total_sat_atleast1_time << "s" << endl;
	cout << "SAT Intersections: " << total_sat_intersection_time << "s" << endl;
	cout << "SAT Encoding: " << sat_total_encode << "s" << endl; // total of covering, intersection and set up
	cout << "SAT Solving: " << total_sat_solving_time << "s" << endl;

	cout << "\nLine Read: " << total_line_read_time << "s" << endl;
	cout << "Line Finding: " << total_line_finding_time << "s" << endl;
	cout << "Line Parallel: " << total_line_parallel_time << "s" << endl;
	cout << "Line Intersection: " << total_line_intersection_time << "s" << endl;

	cout << "\nSAT Total: " << sat_total << "s" << endl;
	cout << "Line Total: " << line_total << "s" << endl;
	cout << "Missing Time: " << elapsed - (sat_total + line_total) << "s" << endl;
#endif

#if MAX_RUNTIME > 0
	cout << "\nMax Runtime: " << MAX_RUNTIME << " seconds\n";
#endif

	return 0;
}

/*
Possible TODO list:
1. see if their is a faster way to read files than ifstream 
	(maybe there is a special one for single core mode where it doesn't save anything to memory? would need to check if memory is even an issue.)

cd /mnt/g/Code/sat\ solver\ stuff/library/
*/
