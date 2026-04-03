#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <unordered_set>
#include <string>
#include <tuple>
#include <chrono>
#include <algorithm>
#include <thread>

#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
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

#define VERIFY_SOLUTION 1

#define TRACK_TIME 1
#define PRINT_TIME 0
#define MAX_RUNTIME 0 // a value below or equal to 0 skips timeout
#define MAX_PARTIAL_SOLUTIONS 2000 // a value below or equal 0 runs all partial solutions

using namespace std;

// Global data structures
const int order = 10;

static vector<int> observed;
static CaDiCaL::Solver solver;

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

__uint128_t all_points_mask; 
vector<__uint128_t> cand_masks_A; 
vector<__uint128_t> cand_masks_B;

uint64_t* overlaps_AA = nullptr;
uint64_t* overlaps_BB = nullptr;

#if TRACK_TIME == 1 // This tracking probably doesn't work the best when we are multithreading, TODO: fix that
double total_sat_solving_time = 0.0; // wall time

double total_line_read_time = 0.0;
double total_line_parse_time = 0.0;
double total_line_finding_time = 0.0;
double total_line_parallel_time = 0.0;
double total_line_intersection_time = 0.0;
double total_line_refinement_time = 0.0;

double total_stream_read_time = 0.0; // time spent in getline() itself
double total_hash_dedup_time = 0.0;  // time spent hashing + seen.insert()
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
 * Each line in the file beginning with 'R' or 'N' is parsed as a list of point indices and converted to a uint64_t. All points encountered across all lines are collected into a set.
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
 * For each symbol in each square, if all `order` assignments are present in the solution, the corresponding line is added as a uint64_t, otherwise line is skipped.
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

    for (int i = 0; i < solution_count; i++) {
        int var = solution[i];
        if (var <= 0) continue;
        const VarInfo& v = var_lookup[var];
        int point = v.r * order + v.c + 1;
        int& cnt = counts[v.sq][v.s];
        if (cnt < order)
            points_by_symbol[v.sq][v.s][cnt++] = point;
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

static void encode_exactly_min_max(CaDiCaL::Solver &solver, vector<int> &var_list, int min, int max, int &var_cnt)
{
    int n = var_list.size();
    int k = max + 1;          // we need s[i][0] ... s[i][max+1]
    int l = min;

    // create s variables: s[i][j] for i=0..n, j=0..k
    vector<vector<int>> s;
    for (int i = 0; i < n + 1; i++) {
        s.push_back(vector<int>());
        for (int j = 0; j < k + 1; j++)
            s[i].push_back(++var_cnt);
    }

    // s[i][0] is always true
    for (int i = 0; i < n + 1; i++) {
        solver.add(s[i][0]);
        solver.add(0);
    }
    // s[0][j] is false for j >= 1
    for (int j = 1; j < k + 1; j++) {
        solver.add(-s[0][j]);
        solver.add(0);
    }
    // at least min: s[n][j] must be true for j = 1..min
    for (int j = 1; j < l + 1; j++) {
        solver.add(s[n][j]);
        solver.add(0);
    }
    // at most max: s[i][max+1] must be false for all i
    for (int i = 1; i < n + 1; i++) {
        solver.add(-s[i][k]);
        solver.add(0);
    }

    // sequential encoding
    for (int i = 1; i < n + 1; i++)
        for (int j = 1; j < k + 1; j++) {
            // forward: s[i-1][j] -> s[i][j]
            solver.add(-s[i-1][j]);
            solver.add(s[i][j]);
            solver.add(0);

            // forward: (x_i and s[i-1][j-1]) -> s[i][j]
            solver.add(-var_list[i-1]);
            solver.add(-s[i-1][j-1]);
            solver.add(s[i][j]);
            solver.add(0);

            // reverse implications (only needed for j <= max, i.e. j < k)
            if (j < k) {
                // s[i][j] -> s[i-1][j] or x_i
                solver.add(-s[i][j]);
                solver.add(s[i-1][j]);
                solver.add(var_list[i-1]);
                solver.add(0);

                // s[i][j] -> (if not x_i then s[i-1][j-1])
                // i.e., s[i][j] and not x_i -> s[i-1][j-1]
                solver.add(-s[i][j]);
                solver.add(-var_list[i-1]);
                solver.add(s[i-1][j-1]);
                solver.add(0);
            }
        }
}

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
	
	for(int i = 0; i < count_B; i++)
		observed.push_back(i+1);

	vector<int> lines_through_points[order * order];
		
	for (int p = 0; p < order * order; p++) {
		for (size_t i = 0; i < count_B; i++) {
			const __uint128_t& m = cand_masks_B[i];  
			if (mask_isSet(m, p))
				lines_through_points[p].push_back(i + 1);
		}
	}

	int var_count = count_B;
	for(int i = 0; i < order * order; i++)
		encode_exactly_min_max(solver, lines_through_points[i], 1, 1, var_count);

	auto end = chrono::steady_clock::now(); 
	double elapsed = chrono::duration<double>(end - start).count();
    cout << "Precomputed SAT Instance using masks in " << elapsed << " seconds." << endl;
	//cout << "  A-B: " << cand_lines_A.size() << "x" << cand_lines_B.size() << " = " << (cand_lines_A.size() * cand_lines_B.size()) << " entries" << endl;
}

/**
 * @brief Verifies that a set of B candidate lines (given as 1-based variable indices) covers all 100 points exactly once.
 * Checks: exactly `order` lines selected, no two lines share a point, union covers all points.
 * @param b_vars 1-based variable indices (positive literals) for the selected B lines.
 * @returns true if valid, false otherwise. Prints a diagnostic to stderr if invalid.
 */
bool verify_b_solution(const vector<int>& b_vars, __uint128_t a_lines[]) {
    if ((int)b_vars.size() != order) {
        cerr << "[VERIFY FAIL] Expected " << order << " B lines, got " << b_vars.size() << "\n";
        return false;
    }

    __uint128_t coverage = 0;
    for (int v : b_vars) {
        int idx = v - 1; // 0-based
        if (idx < 0 || idx >= count_B) {
            cerr << "[VERIFY FAIL] B variable " << v << " out of range [1," << count_B << "]\n";
            return false;
        }
        __uint128_t m = cand_masks_B[idx];
		for(int i=0; i < 10; i++)
			if (!intersectsExactlyOnce(a_lines[i], m))
			{
				cerr << "[VERIFY FAIL] B line " << v << " intersects more than or less than once with A square\n";
				mask_print(a_lines[i]);
				mask_print(m);
				return false;
			}
        if ((coverage & m) != 0) {
            cerr << "[VERIFY FAIL] B line " << v << " overlaps with a previously selected line\n";
            return false;
        }
        coverage |= m;
    }

    __uint128_t expected = ((__uint128_t)1 << (order * order)) - 1; // 100 bits
    if (coverage != expected) {
        cerr << "[VERIFY FAIL] Coverage mask does not cover all 100 points\n";
        uint64_t lo = (uint64_t)coverage;
        uint64_t hi = (uint64_t)(coverage >> 64);
        uint64_t exp_lo = (uint64_t)expected;
        uint64_t exp_hi = (uint64_t)(expected >> 64);
        cerr << "  lo: " << hex << lo << " (expected " << exp_lo << ")\n";
        cerr << "  hi: " << hex << hi << " (expected " << exp_hi << ")\n" << dec;
        return false;
    }
    return true;
}

struct CaptureResult {
	int solutions_checked = 0;
	int solutions_invalid = 0;
};

/**
 * @brief Redirects stdout at the fd level into a pipe, tees output back to the real
 * terminal in real time, then parses and verifies every "c New solution:" line.
 * Works for printf, cout, or any other stdout output from the propagator.
 */
static CaptureResult capture_and_verify_solve(CaDiCaL::Solver& s, long int& sol_count_out, ExhaustiveSearch& propagator, __uint128_t a_vars[]) {
	int saved_stdout = dup(STDOUT_FILENO);
	int pipefd[2];
	pipe(pipefd);

	cout.flush();
	fflush(stdout);
	dup2(pipefd[1], STDOUT_FILENO);
	close(pipefd[1]);

	CaptureResult result;
	string captured;
	thread tee([&]() {
		char buf[4096];
		ssize_t n;
		while ((n = read(pipefd[0], buf, sizeof(buf))) > 0) {
			write(saved_stdout, buf, n);
			captured.append(buf, n);
		}
	});

	s.solve();
	sol_count_out = propagator.get_solution_count();

	fflush(stdout);
	dup2(saved_stdout, STDOUT_FILENO);
	close(saved_stdout);
	close(pipefd[0]);
	tee.join();
	cout.clear();

	const string prefix = "c New solution:";
	istringstream stream(captured);
	string line;
	while (getline(stream, line)) {
		if (line.rfind(prefix, 0) != 0) continue;
		++result.solutions_checked;
		istringstream iss(line.substr(prefix.size()));
		vector<int> b_vars;
		int v;
		while (iss >> v)
			if (v > 0 && v <= count_B)
				b_vars.push_back(v);
		if (!verify_b_solution(b_vars, a_vars))
			++result.solutions_invalid;
	}

	return result;
}

int get_refinements(const int& trans_A, const int& trans_B, const int A_sol_lines[], const int B_indices[], __uint128_t A_masks[]) {
    // 1. Assume the B lines that are already fixed in the partial solution
    for (int i = 0; i < trans_B; i++)
        solver.assume(B_indices[i] + 1);
#if TRACK_TIME == 1
	auto timer = chrono::steady_clock::now();
#endif
    // 2. If there are any A lines, filter the remaining B lines using the precomputed bitset
    if (trans_A > 0) {
        // Allocate a bitset covering all B lines, initially all ones
        uint64_t* result = (uint64_t*)alloca(rows_B * sizeof(uint64_t));
        memset(result, 0xFF, rows_B * sizeof(uint64_t));

        // Intersect the rows of intersects_once_BA for each A line
        for (int i = 0; i < trans_A; i++) {
            const uint64_t* row = intersects_once_BA + (long long)A_sol_lines[i] * rows_B;
            for (int w = 0; w < rows_B; w++)
                result[w] &= row[w];
        }

        // For each B line, if it is not fixed and not in the intersection, assume it false
        for (int j = 0; j < count_B; j++) {
            // Check if j is one of the fixed B lines
            bool is_fixed = false;
            for (int k = 0; k < trans_B; k++) {
                if (B_indices[k] == j) {
                    is_fixed = true;
                    break;
                }
            }
            if (is_fixed)
                continue;
            // Test the bit in the computed result
            if (!((result[j / 64] >> (j % 64)) & 1))
                solver.assume(-(j + 1));
        }
    } 

#if TRACK_TIME == 1
	double elapsed_3 = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	total_line_intersection_time += elapsed_3;
	timer = chrono::steady_clock::now();
#endif

    ExhaustiveSearch propagator(&solver, observed, true, nullptr, false);

	long int sol_count = 0;
#if VERIFY_SOLUTION == 1
	CaptureResult verify = capture_and_verify_solve(solver, sol_count, propagator, A_masks);
    int valid = verify.solutions_checked - verify.solutions_invalid;
    if (verify.solutions_checked == 0 && sol_count > 0)
        cerr << "[VERIFY] WARNING: " << sol_count << " solution(s) counted but 0 'c New solution:' lines intercepted.\n";
    else if (verify.solutions_checked > 0) {
        cerr << "[VERIFY] " << valid << "/" << verify.solutions_checked << " solutions valid";
        if (verify.solutions_invalid > 0)
            cerr << " -- " << verify.solutions_invalid << " INVALID!";
        cerr << "\n";
    }
#else
	solver.solve();
	sol_count = propagator.get_solution_count();
#endif

#if TRACK_TIME == 1
    double solver_elapsed = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	total_sat_solving_time += solver_elapsed;
#endif

    return sol_count;
}

int processLine(string& line)
{
#if TRACK_TIME == 1
	auto read_time = chrono::steady_clock::now();
#endif 
	if (line.empty()) 
		return 0;
	if (line.back() == '0') {
		line.pop_back();
	}
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
	total_line_read_time += elapsed_0;
#endif 

	__uint128_t A_sol_lines[order];
    int trans_A = 0;
    __uint128_t B_sol_lines[order];
    int trans_B = 0;

    solutionToCandidateLines(solution, solution_count, A_sol_lines, trans_A, B_sol_lines, trans_B);

#if TRACK_TIME == 1
	double elapsed_1 = chrono::duration<double>(chrono::steady_clock::now() - conversion_time).count();
	auto refinement_time = chrono::steady_clock::now();
	total_line_parse_time += elapsed_1;
#endif
	
	// Convert solution lines to their candidate line indices
	int A_sol_indices[trans_A];
	int B_sol_indices[trans_B];
	for (int i = 0; i < trans_A; i++)
		A_sol_indices[i] = cand_hash_A[A_sol_lines[i]];
	for (int i = 0; i < trans_B; i++)
		B_sol_indices[i] = cand_hash_B[B_sol_lines[i]];


	long int refinement_count = get_refinements(trans_A, trans_B, A_sol_indices, B_sol_indices, A_sol_lines);
	
#if TRACK_TIME == 1
	double elapsed_2 = chrono::duration<double>(chrono::steady_clock::now() - refinement_time).count();
	total_line_refinement_time += elapsed_2;
#endif 

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
	
	long long total_refinements = 0;

	unordered_set<size_t> seen;
	seen.reserve(2000000);

	int fd = open(solution_file.c_str(), O_RDONLY);
	if (fd < 0) { cerr << "Cannot open: " << solution_file << "\n"; return 1; }
	struct stat sb;
	fstat(fd, &sb);
	size_t file_size = sb.st_size;
	const char* data = (const char*)mmap(nullptr, file_size, PROT_READ, MAP_PRIVATE, fd, 0);
	close(fd);
	madvise((void*)data, file_size, MADV_SEQUENTIAL); // hint to kernel: read ahead

	const char* p   = data;
	const char* end = data + file_size;
	
	start_time = chrono::steady_clock::now();
	#if ENABLE_MT == 0
		while (p < end) {
			#if TRACK_TIME == 1
			auto stream_time = chrono::steady_clock::now();
			#endif
			const char* nl = (const char*)memchr(p, '\n', end - p);
			const char* line_end = nl ? nl : end;
			size_t len = line_end - p; 
			if (len > 0 && p[len-1] == '\r') len--; // trim trailing \r for Windows line endings
			#if TRACK_TIME == 1
			total_stream_read_time += chrono::duration<double>(chrono::steady_clock::now() - stream_time).count();
			#endif

			if (len > 0) {
				#if TRACK_TIME == 1
				auto hash_time = chrono::steady_clock::now();
				#endif
				size_t h = 14695981039346656037ULL; // hash inline — no string allocation at all
				for (size_t i = 0; i < len; i++)
					h = (h ^ (unsigned char)p[i]) * 1099511628211ULL;
				bool is_new = seen.insert(h).second;
				#if TRACK_TIME == 1
				total_hash_dedup_time += chrono::duration<double>(chrono::steady_clock::now() - hash_time).count();
				#endif
				if (is_new) {
					string line(p, len);
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
					if(MAX_PARTIAL_SOLUTIONS > 0 && partial_count > MAX_PARTIAL_SOLUTIONS)
						break;
				}
			}
    		p = nl ? nl + 1 : end;
		}
		munmap((void*)data, file_size);
		cout << "\n";
	#else
		struct LineInfo { const char* start; size_t len; };
		vector<LineInfo> unique_lines;
		unique_lines.reserve(1500000);
		
		while (p < end) {
			#if TRACK_TIME == 1
			auto stream_time = chrono::steady_clock::now();
			#endif
			const char* nl = (const char*)memchr(p, '\n', end - p);
			const char* line_end = nl ? nl : end;
			size_t len = line_end - p;
			if (len > 0 && p[len-1] == '\r') len--;   // trim CR
			#if TRACK_TIME == 1
			total_stream_read_time += chrono::duration<double>(chrono::steady_clock::now() - stream_time).count();
			#endif

			if (len > 0) {
				#if TRACK_TIME == 1
				auto hash_time = chrono::steady_clock::now();
				#endif
				size_t h = 14695981039346656037ULL; // FNV‑1a hash
				for (size_t i = 0; i < len; ++i)
					h = (h ^ (unsigned char)p[i]) * 1099511628211ULL;
				bool is_new = seen.insert(h).second;
				#if TRACK_TIME == 1
				total_hash_dedup_time += chrono::duration<double>(chrono::steady_clock::now() - hash_time).count();
				#endif
				if (is_new) {
					unique_lines.push_back({p, len});
				}
			}
			p = nl ? nl + 1 : end;
		}
		
		cout << "Loaded " << unique_lines.size() << " solutions to process.\n"; // show add a timer for this to display how long this took
			
		atomic<bool> abort_early(false);

		auto max_threads = omp_get_max_threads();
		int limit_threads = 2;
		int curr_threads = max(1, max_threads - limit_threads);

		omp_set_num_threads(curr_threads);
		
		start_time = chrono::steady_clock::now();
		#pragma omp parallel for schedule(dynamic)
		for (size_t sol_idx = 0; sol_idx < unique_lines.size(); sol_idx++)
			if (!abort_early) {
        		const LineInfo& li = unique_lines[sol_idx];
        		string line(li.start, li.len);          // copy to mutable string
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
	double line_total = total_line_read_time + total_line_parse_time + total_line_finding_time + total_line_parallel_time + total_line_intersection_time;
	double io_total = total_stream_read_time + total_hash_dedup_time;

	cout << "\n=== TOTAL TIMES FOR THIS RUN ===\n";
	cout << "SAT Solving: " << total_sat_solving_time << "s" << endl;

	cout << "\nStream Read: " << total_stream_read_time << "s" << endl;
	cout << "Hash Dedup: " << total_hash_dedup_time << "s" << endl;
	
	cout << "\nLine Read: " << total_line_read_time << "s" << endl;
	cout << "Line Parsing: " << total_line_parse_time << "s" << endl;
	cout << "Line Finding: " << total_line_finding_time << "s" << endl;
	cout << "Line Parallel: " << total_line_parallel_time << "s" << endl;
	cout << "Line Intersection: " << total_line_intersection_time << "s (contained within refinement time)" << endl;

	cout << "\nRefinement Total: " << total_line_refinement_time << "s" << endl;
	cout << "IO Total: " << io_total << "s" << endl;
	cout << "Line Total: " << line_total << "s" << endl;
	cout << "Missing Time: " << elapsed - (total_sat_solving_time + line_total + io_total) << "s" << endl;
#endif

#if MAX_RUNTIME > 0
	cout << "\nMax Runtime: " << MAX_RUNTIME << " seconds\n";
#endif

#if MAX_PARTIAL_SOLUTIONS > 0
	cout << "\nMax Partial Solutions: " << MAX_PARTIAL_SOLUTIONS << " seconds\n";
#endif

	return 0;
}
