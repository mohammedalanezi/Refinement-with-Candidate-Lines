extern "C" {
#include "exact.h"
}

#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <string>
#include <cstring>
#include <tuple>
#include <chrono>
#include <algorithm>

#include <fcntl.h>
#include <unistd.h>
#include <cstdlib>

#define TRACK_TIME 1

using namespace std;

// Global data structures
#ifndef ORDER_DEFINED
#define ORDER_DEFINED
const int order = 10;
#endif

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
long total_refinements = 0;
int count_A = 0;
int count_B = 0;

__uint128_t all_points_mask; // bit (p-1) set means point p is on this line (points 1–100, so bits 0–99 used)

vector<__uint128_t> cand_masks_A; 
vector<__uint128_t> cand_masks_B;

static int* intersecting_B_buf = nullptr;

#if TRACK_TIME == 1 // This tracking probably doesn't work the best when we are multithreading, TODO: fix that
double total_libexact_creation_time = 0.0;
double total_libexact_solve_time = 0.0;

double file_load_time = 0.0;
double precompute_time = 0.0;

double total_line_parse_time = 0.0;
double total_line_finding_time = 0.0;
double total_line_intersection_time = 0.0;

double total_early_parse_time = 0.0;
double total_early_finding_time = 0.0;
double total_early_intersection_time = 0.0;
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
unordered_map<__uint128_t, int, U128Hash> cand_hash_B;

struct VarInfo { int8_t sq, r, c, s; }; // 4 bytes per entry
VarInfo var_lookup[2 * order * order * order + 1]; // index by var (1-based)

auto start_time = chrono::steady_clock::now(); // Precompute masks

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
 * @brief Precomputes all data structures needed for fast per-solution filtering and SAT encoding.
 *
 * Builds four bitset tables, all in flat row-major layout where each row is a bitset over the lines of one square packed into 64-bit words:
 *
 *  - `intersects_once_AB[j * rows_A + w]`: bit i set iff A line i intersects B line j exactly once,
 *
 *  - `intersects_once_BA[i * rows_B + w]`: bit j set iff B line j intersects A line i exactly once
 *    (both transposes of each other, allows us row-major access from either direction).
 *
 *
 * With ~14k lines per side, intersects_once_AB/BA are ~24MB each.Both fit in L3 cache, keeping the bit lookups fast across all tens of millions of calls.
 *
 * Also initialises:
 * 
 *  - `all_line_indices_A/B`: identity index arrays [0, 1, ..., count-1] used as the default candidate set when no filtering has been applied.
 * 
 *  - `cand_hash_A/B`: __uint128_t-to-index lookup maps for resolving solution lines to their global candidate indices.
 * 
 *  - `var_lookup`: int to 4 tuple look up map, used to avoid needing to divide multiple times per line.
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

	all_line_indices_A = new int[count_A];
	for(int i = 0; i < count_A; i++)
		all_line_indices_A[i] = i;
	all_line_indices_B = new int[count_B];
	for(int i = 0; i < count_B; i++)
		all_line_indices_B[i] = i;

	cand_hash_A.reserve(count_A * 2); // halves load factor so we have 2x fewer collision chains
	for (int i = 0; i < count_A; ++i)
		cand_hash_A[cand_masks_A[i]] = i;
	cand_hash_B.reserve(count_B * 2);
	for (int i = 0; i < count_B; ++i)
		cand_hash_B[cand_masks_B[i]] = i;

	for (int var = 1; var <= 2 * order * order * order; var++) {
		auto [sq, r, c, s] = indexTo4Tuple(var, 2, order, order, order);
		var_lookup[var] = { (int8_t)sq, (int8_t)r, (int8_t)c, (int8_t)s };
	}

	auto end = chrono::steady_clock::now();
	double elapsed = chrono::duration<double>(end - start).count();
	cout << "Precomputed intersections using masks in " << elapsed << " seconds." << endl;
	//cout << "  A-B: " << cand_lines_A.size() << "x" << cand_lines_B.size() << " = " << (cand_lines_A.size() * cand_lines_B.size()) << " entries" << endl;
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
void solutionToCandidateLines(const vector<int>& solution, __uint128_t a_lines[], int& a_solutions) {
	int points_by_symbol[2][order][order] = {0};
	int counts[2][order] = {0};

	for(int var : solution) {
		if (var < 1 || var > 2 * order * order * order) continue;
		const VarInfo& v = var_lookup[var]; 
		int point = v.r * order + v.c + 1;
		int& cnt = counts[v.sq][v.s];
		points_by_symbol[v.sq][v.s][cnt++] = point;
	}

	for (int sq = 0; sq < 2; ++sq)
		for (int s = 0; s < order; ++s)
			if (counts[sq][s] == order) {
				if (sq == 0) 
					a_lines[a_solutions++] = make_mask(points_by_symbol[sq][s]);
			}
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

	for (int w = 0; w < rows_B; ++w) {
		uint64_t word = result[w];
		if (!word) continue;  // skip entire 64-bit zero word
		while (word) {
			int bit = __builtin_ctzll(word);
			int idx = w * 64 + bit;
			if (idx >= count_B) return;
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

	for (int w = 0; w < rows_B; ++w) {
		uint64_t word = result[w];
		if (!word) continue;  // skip entire 64-bit zero word
		while (word) {
			int bit = __builtin_ctzll(word);
			int idx = w * 64 + bit;
			if (idx >= count_B) return;
			union_mask |= masks[idx];
			if (union_mask == all_points_mask) return;
			word &= word - 1;
		}
	}
}

/**
 * @brief Counts valid refinements using libexact exhaustive exact cover search.
 *
 * Sets up an exact cover instance with 200 rows (100 grid points for A, 100 for B) and
 * A_count + B_count columns (one per candidate line). 
 * 
 * Each candidate line declares entries for the grid points it covers. libexact then enumerates 
 * all ways to choose order non-overlapping A lines that cover all 100 A points, paired with 
 * order non-overlapping B lines that cover all 100 B points. 
 *
 * @param trans_A   Number of A lines already determined by the partial solution.
 * @param trans_B   Number of B lines already determined by the partial solution.
 * @param A_indices Candidate A line indices that passed parallel + intersection filtering.
 * @param A_count   Number of candidate A lines.
 * @param B_indices Candidate B line indices that passed parallel + intersection filtering.
 * @param B_count   Number of candidate B lines.
 * @param union_A   OR of all masks in A_indices (precomputed, 0 if trans_A == order).
 * @param union_B   OR of all masks in B_indices (precomputed, 0 if trans_B == order).
 * @returns The total number of valid refinements found.
 */
int get_refinements(const int B_indices[], const int& B_count, const __uint128_t union_B) {
#if TRACK_TIME == 1
	auto timer = chrono::steady_clock::now();
#endif
	if (union_B != all_points_mask) {
		#if TRACK_TIME == 1
		total_libexact_creation_time += chrono::duration<double>(chrono::steady_clock::now() - timer).count();
		#endif
		return -1;
	}

	if (B_count == order) return 1;

	exact_t* e = exact_alloc();

	// 1. declare rows: 100 grid points for B
	for (int p = 0; p < order * order; p++) { // each point must be covered by exactly one line in its respective square
		exact_declare_row(e, p + 1, 1);
	}

	// 2. declare columns: B candidate lines (colmum IDs 1...B_count)
	for (int i = 0; i < B_count; i++)
		exact_declare_col(e, i + 1, 1);

#if TRACK_TIME == 1
	double creation_elapsed = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	timer = chrono::steady_clock::now();
#endif

	// 3. declare entries for B lines: for each B candidate, record which grid points it covers
	for (int i = 0; i < B_count; i++) {
		__uint128_t mask = cand_masks_B[B_indices[i]];
		uint64_t lo = (uint64_t)mask;
		uint64_t hi = (uint64_t)(mask >> 64);
		while (lo) { int b = __builtin_ctzll(lo); exact_declare_entry(e, b + 1, i + 1); lo &= lo - 1; }
		while (hi) { int b = __builtin_ctzll(hi); exact_declare_entry(e, 64 + b + 1, i + 1); hi &= hi - 1; }
	}

#if TRACK_TIME == 1
	total_libexact_creation_time += creation_elapsed + chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	timer = chrono::steady_clock::now();
#endif

	// 4. enumerate all solutions: each solution is a valid B square
	int soln_size;
	const int* soln;
	long int sol_count = 0;
	while ((soln = exact_solve(e, &soln_size)) != NULL)
		sol_count++;
	exact_free(e);

#if TRACK_TIME == 1
	total_libexact_solve_time += chrono::duration<double>(chrono::steady_clock::now() - timer).count();
#endif

	return sol_count;
}

long int get_refinement_count() {
	return total_refinements;
}

long int get_skipped_count() {
	return skipped_partial_solutions;
}

int setup(int template_id) {
	cout << "Loading candidate lines from files..." << endl;

	string parent_dir = "../refinements and candidate lines/";
	string candidate_lines_2_path = parent_dir + "2-candidate_lines/" + to_string(template_id) + "-candidate_lines.txt";
	string candidate_lines_3_path = parent_dir + "3-candidate_lines/" + to_string(template_id) + "-candidate_lines.txt";

	tie(cand_masks_A, points_A, count_A) = load_candidate_lines_file(candidate_lines_2_path);
	tie(cand_masks_B, points_B, count_B) = load_candidate_lines_file(candidate_lines_3_path);

	total_points = points_A;
	total_points.insert(points_B.begin(), points_B.end());
	
	intersecting_B_buf = new int[count_B];
	
	file_load_time = chrono::duration<double>(chrono::steady_clock::now() - start_time).count();
	
	cout << "Precomputing all data structures..." << endl;
	precomputeDataStructures();
	
	precompute_time = chrono::duration<double>(chrono::steady_clock::now() - start_time).count() - file_load_time;

	return 0;
}

int processLine(const int sym_A_idx[order]) {
    ++partial_count;

    #if TRACK_TIME == 1
    auto intersection_time = chrono::steady_clock::now();
    #endif

    int intersection_B_count = 0;
    __uint128_t union_B = 0;
    getIntersectingBLineIndices(intersecting_B_buf, intersection_B_count, sym_A_idx, union_B);

    #if TRACK_TIME == 1
    double elapsed_3 = chrono::duration<double>(chrono::steady_clock::now() - intersection_time).count();
    total_line_intersection_time += elapsed_3;
    #endif

    if (intersection_B_count < order)
        return -1;

    return get_refinements(intersecting_B_buf, intersection_B_count, union_B);
}

bool check_partial_solution_covering(const int sym_A_idx[order]) {
    #if TRACK_TIME == 1
    auto intersection_time = chrono::steady_clock::now();
    #endif

    __uint128_t union_B = 0;
    getIntersectingBCovering(sym_A_idx, union_B);

    #if TRACK_TIME == 1
    double elapsed_3 = chrono::duration<double>(chrono::steady_clock::now() - intersection_time).count();
    total_early_intersection_time += elapsed_3;
    #endif

    return union_B == all_points_mask;
}

bool solve_partial_solution(const int sym_A_idx[order]) {
    long int refinement_count = processLine(sym_A_idx);
    if (refinement_count > 0) {
        total_refinements += refinement_count;
        return false;
    } else if (refinement_count < 0)
        skipped_partial_solutions += 1;
    return true;
}

void print_substep_timings_log(double creation_time,
		double total_minimize_convert, double total_minimize_cleanup, double total_minimize_remove,
		double total_cube_gen_time, double total_cube_creation_time, double total_cube_solve_time) {
	double elapsed = chrono::duration<double>(chrono::steady_clock::now() - start_time).count();

	cout << "\n======= SUBSTEP DEFINITION  =======\n";
	cout << "When a partial solution is found in the SAT instance, we attempt to refine it into all its possible full solutions.\n";
	cout << "While looking for partial solutions, if they are incomplete, then we check if they can extend to a full solution and block early if they cannot.\n";
	cout << "Each partial solution goes through a filter to process its compatible candidate lines, after which, these lines are checked to see if a solution is possible; skipping impossible partial solutions.\n";
	cout << "Afterwards, the filtered candidate lines are created into a libexact instance and solved for all their possible refinements.\n";
	cout << "Early blocking clauses and blocking clauses of partial solutions with no refinement are minimized to keep their clauses short.\n";

#if TRACK_TIME == 1
	double input_total = file_load_time + precompute_time;
	double libexact_total = total_libexact_creation_time + total_libexact_solve_time;
	double line_total =  total_line_parse_time + total_line_finding_time + total_line_intersection_time;
	double substep_total = line_total + libexact_total + input_total;

	double early_total =  total_early_parse_time + total_early_finding_time + total_early_intersection_time;
	double minimize_total = total_minimize_convert + total_minimize_cleanup + total_minimize_remove;
	double post_processing = early_total + minimize_total;
	
	double sat_internal = total_cube_solve_time - (early_total + minimize_total + substep_total);
	double cubing_total = total_cube_gen_time + total_cube_creation_time + sat_internal;
	
    double accounted = creation_time + cubing_total + substep_total + post_processing;
    double other = elapsed - accounted;

	cout << "\n=== WALL TIMINGS ===\n";
	cout << "   Cube (SAT -> Solving + Early -> Minimize) -> Substep (INPUT -> FILTER -> LIBEXACT)\n";
	
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
	
	cout << "Early:\n";
	cout << "   Conversion to Candidate Lines: " << total_early_parse_time << "s\n";
	cout << "   Candidate Index Lookup: " << total_early_finding_time << "s\n";
	cout << "   Keep Valid Intersecting Lines: " << total_early_intersection_time << "s\n";
	cout << "   Total: " << early_total << "s\n";
	
	cout << "Minimize:\n";
	cout << "   Parse Clauses to Lines: " << total_minimize_convert << "s\n";
	cout << "   Remove Partial Lines: " << total_minimize_cleanup << "s\n";
	cout << "   Remove Redundant Lines: " << total_minimize_remove << "s\n";
	cout << "   Total: " << minimize_total << "s\n";

	cout << "\nInput:\n";
	cout << "   Reading from Candidate Lines files took: " << file_load_time << "s\n";
	cout << "   Precomputing the required datastructures took: " << precompute_time << "s\n";
	cout << "   Total: " << input_total << "s\n";

	cout << "Filter:\n";
	cout << "   Parse Partial Solutions: " << total_line_parse_time << "s\n";
	cout << "   Conversion to Candidate Lines: " << total_line_finding_time << "s\n";
	cout << "   Keep Valid Intersecting Lines: " << total_line_intersection_time << "s\n";
	cout << "   Total: " << line_total << "s\n";

	cout << "Libexact:\n";
	cout << "   Libexact Creation: " << total_libexact_creation_time << "s\n";
	cout << "   Libexact Solving: " << total_libexact_solve_time << "s\n";
	cout << "   Total: " << libexact_total << "s\n";

	cout << "Substep Total: " << line_total + libexact_total + input_total << "s\n";
	cout << "Total: " << elapsed << "s\n";
	cout << "Other/Extra: " << other << "s\n";
#endif
}