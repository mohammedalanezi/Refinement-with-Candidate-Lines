/**
 * all_candidate_encoding.cpp
 *
 * C++ port of all_candidate_encoding.py.
 *
 * Builds a single global SAT instance over ALL candidate lines for both
 * parallel classes and exhaustively enumerates all valid combinations, 
 * i.e. all pairs of complete transversals (one from each class) that
 * together cover every point exactly once and cross-intersect exactly once.
 *
 * Usage: ./all_candidate_encoding <solution_path> <template_id>
 */

#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <string>
#include <tuple>
#include <chrono>
#include <algorithm>
#include <cstdlib>

#include "cadical.hpp"
#include "exhaustive.hpp"

using namespace std;

// ---------------------------------------------------------------
// Constants
// ---------------------------------------------------------------

const int order = 10;

// ---------------------------------------------------------------
// Global data structures (mirrors the baseline layout)
// ---------------------------------------------------------------

unordered_set<int> points_A, points_B, total_points;
vector<__uint128_t> cand_masks_A, cand_masks_B;
int count_A = 0, count_B = 0;

// intersects_once_AB[j * rows_A + w]: bit i set iff A[i] intersects B[j] exactly once
uint64_t* intersects_once_AB = nullptr;
int rows_A = 0, rows_B = 0;

// overlaps_AA[i * rows_A + w]: bit j set iff A[i] and A[j] share >= 1 point
uint64_t* overlaps_AA = nullptr;
uint64_t* overlaps_BB = nullptr;

__uint128_t all_points_mask; // bits 0–99 set

// point_to_A[p] / point_to_B[p] : 0-based point index → list of line indices covering it
vector<vector<int>> point_to_A;
vector<vector<int>> point_to_B;

// ---------------------------------------------------------------
// Utility helpers
// ---------------------------------------------------------------

struct U128Hash {
	size_t operator()(__uint128_t v) const {
		uint64_t lo = (uint64_t)v, hi = (uint64_t)(v >> 64);
		lo ^= lo >> 33; lo *= 0xff51afd7ed558ccdULL; lo ^= lo >> 33;
		hi ^= hi >> 33; hi *= 0xc4ceb9fe1a85ec53ULL; hi ^= hi >> 33;
		return lo ^ (hi * 0x9e3779b97f4a7c15ULL);
	}
};

__uint128_t make_mask(const vector<int>& line) {
	__uint128_t m = 0;
	for (int x : line)
		m |= ((__uint128_t)1 << (x - 1));
	return m;
}

bool intersectsExactlyOnce(__uint128_t m1, __uint128_t m2) {
	__uint128_t c = m1 & m2;
	return c != 0 && (c & (c - 1)) == 0;
}

bool linesIntersect(__uint128_t m1, __uint128_t m2) {
	return (m1 & m2) != 0;
}

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
 * @brief Loads candidate lines from a text file.
 * Lines beginning with 'R' or 'N' are parsed as space-separated point lists
 * and converted to __uint128_t bitmasks. All point values are collected.
 */
tuple<vector<__uint128_t>, unordered_set<int>, int>
load_candidate_lines_file(const string& path) {
	ifstream f(path);
	if (!f.is_open()) {
		cerr << "Cannot open candidate lines file: " << path << "\n";
		return {{}, {}, 0};
	}
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

// ---------------------------------------------------------------
// Precomputation
// ---------------------------------------------------------------

/**
 * @brief Precomputes all bitset tables and point-to-line index maps.
 *
 * Builds:
 *   intersects_once_AB  — for fast cross-intersection constraint generation
 *   overlaps_AA / BB    — for fast no-overlap (at-most-one) constraint generation
 *   point_to_A / B      — for fast at-least-one (coverage) clause generation
 */
void precomputeDataStructures() {
	auto start = chrono::steady_clock::now();

	all_points_mask = ((__uint128_t)1 << 100) - 1;

	rows_A = (count_A + 63) / 64;
	rows_B = (count_B + 63) / 64;

	// --- Exact-once cross-intersection bitset ---
	intersects_once_AB = new uint64_t[(long long)count_B * rows_A]();
	for (int i = 0; i < count_A; ++i)
		for (int j = 0; j < count_B; ++j)
			if (intersectsExactlyOnce(cand_masks_A[i], cand_masks_B[j]))
				intersects_once_AB[(long long)j * rows_A + i / 64] |= (1ULL << (i % 64));

	// --- Overlap bitsets (symmetric) ---
	overlaps_AA = new uint64_t[(long long)count_A * rows_A]();
	for (int i = 0; i < count_A; i++)
		for (int j = i + 1; j < count_A; j++)
			if (linesIntersect(cand_masks_A[i], cand_masks_A[j])) {
				overlaps_AA[(long long)i * rows_A + j / 64] |= (1ULL << (j % 64));
				overlaps_AA[(long long)j * rows_A + i / 64] |= (1ULL << (i % 64));
			}

	overlaps_BB = new uint64_t[(long long)count_B * rows_B]();
	for (int i = 0; i < count_B; i++)
		for (int j = i + 1; j < count_B; j++)
			if (linesIntersect(cand_masks_B[i], cand_masks_B[j])) {
				overlaps_BB[(long long)i * rows_B + j / 64] |= (1ULL << (j % 64));
				overlaps_BB[(long long)j * rows_B + i / 64] |= (1ULL << (i % 64));
			}

	// --- Point-to-line index maps (0-based point indices) ---
	// Bit b in a mask corresponds to 0-based point b (1-based point b+1).
	point_to_A.resize(order * order);
	for (int i = 0; i < count_A; i++) {
		uint64_t lo = (uint64_t)cand_masks_A[i];
		uint64_t hi = (uint64_t)(cand_masks_A[i] >> 64);
		while (lo) { int b = __builtin_ctzll(lo); point_to_A[b].push_back(i);      lo &= lo - 1; }
		while (hi) { int b = __builtin_ctzll(hi); point_to_A[64 + b].push_back(i); hi &= hi - 1; }
	}

	point_to_B.resize(order * order);
	for (int i = 0; i < count_B; i++) {
		uint64_t lo = (uint64_t)cand_masks_B[i];
		uint64_t hi = (uint64_t)(cand_masks_B[i] >> 64);
		while (lo) { int b = __builtin_ctzll(lo); point_to_B[b].push_back(i);      lo &= lo - 1; }
		while (hi) { int b = __builtin_ctzll(hi); point_to_B[64 + b].push_back(i); hi &= hi - 1; }
	}

	double elapsed = chrono::duration<double>(chrono::steady_clock::now() - start).count();
	cout << "Precomputed data structures in " << elapsed << "s.\n";
}

// ---------------------------------------------------------------
// SAT encoding and exhaustive solving
// ---------------------------------------------------------------

static void encode_exactly_min_max(CaDiCaL::Solver &solver, vector<int> &var_list, int min, int max, int offset)
{
	int n = var_list.size();
	int k = max + 1;
	int l = min;

	vector<vector<int>> s;
	for(int i = 0; i < n + 1; i++) {
		s.push_back(vector<int>());
		for(int j = 0; j < k + 1; j++)
			s[i].push_back(solver.declare_one_more_variable());
	}

	for(int i = 0; i < n + 1; i++) 
	{
		solver.add(s[i][0]);
		solver.add(0);
	}
	for(int j = 1; j < k + 1; j++) 
	{
		solver.add(-s[0][j]);
		solver.add(0);
	}
	for(int j = 1; j < l + 1; j++) 
	{
		solver.add(s[n][j]);
		solver.add(0);
	}
	for(int i = 1; i < n + 1; i++) 
	{
		solver.add(-s[i][k]);
		solver.add(0);
	}

	for(int i = 1; i < n + 1; i++) 
	{
		for(int j = 1; j < k + 1; j++) 
		{
			solver.add(-s[i - 1][j]);
			solver.add(s[i][j]);
			solver.add(0);
			solver.add(-(offset + var_list[i - 1]));
			solver.add(-s[i - 1][j - 1]);
			solver.add(s[i][j]);
			solver.add(0);
			if (j <= l)
			{
				solver.add(-s[i][j]);
				solver.add(s[i - 1][j]);
				solver.add(offset + var_list[i - 1]);
				solver.add(0);
				solver.add(-s[i][j]);
				solver.add(s[i - 1][j - 1]);
				solver.add(0);
			}
		}
	}
}

long long build_and_solve(const string& solution_path, bool can_forget) {
	CaDiCaL::Solver solver;
	solver.set("factor", 0);
	solver.set("factorcheck", 0);
	solver.set("report", 1);
	solver.set("inprocessing", 0);
	solver.set("quiet", 0);
	solver.set("verbose", 1);

	cout << "Building SAT encoding...\n";
	auto encode_start = chrono::steady_clock::now();

	long long n_cross  = 0;

	solver.declare_more_variables(count_A + count_B);

	// ---- 1. Exactly-one coverage clauses for A ----
	for (int p = 0; p < order * order; p++) {
		const auto& covers = point_to_A[p];
		if (covers.empty()) continue;
		encode_exactly_min_max(solver, point_to_A[p], 1, 1, 1);
	}
	cout << "  Finished Exactly-one coverage clauses for A\n";

	// ---- 2. Exactly-one coverage clauses for B ----
	for (int p = 0; p < order * order; p++) {
		const auto& covers = point_to_B[p];
		if (covers.empty()) continue;
		encode_exactly_min_max(solver, point_to_B[p], 1, 1, 1 + count_A);
	}
	cout << "  Finished Exactly-one coverage clauses for B\n";

	// ---- 3. Cross-intersection clauses ----
	// For every (A line i, B line j) pair that does NOT intersect exactly once, add the implication a[i] => NOT b[j], i.e. clause (-a[i] ∨ -b[j]).
	for (int i = 0; i < count_A; i++)
		for (int j = 0; j < count_B; j++)
			if (!((intersects_once_AB[(long long)j * rows_A + i / 64] >> (i % 64)) & 1)) {
				solver.clause(-(i + 1), -(count_A + j + 1));
				++n_cross;
			}
	cout << "  Cross-intersection: " << n_cross << " clauses\n";

	double encode_elapsed = chrono::duration<double>(chrono::steady_clock::now() - encode_start).count();
	cout << "Encoding done in " << encode_elapsed << "s. Vars: " << (count_A + count_B) << ".\n";

	// ---- Observed variables: all A-line variables (1..count_A) ----
	vector<int> observed;
	observed.reserve(count_A);
	for (int i = 1; i <= count_A; i++)
		observed.push_back(i);

	cout << "Running exhaustive SAT solver (observing " << observed.size() << " A-line variables)...\n";

	FILE* fp = fopen(solution_path.c_str(), "w");
	ExhaustiveSearch propagator(&solver, observed, can_forget, nullptr, false, false);

	auto solve_start = chrono::steady_clock::now();
	int result = solver.solve();
	double solve_elapsed = chrono::duration<double>(chrono::steady_clock::now() - solve_start).count();

	long long sol_count = propagator.get_solution_count();

	cout << "SAT result   : " << (result == 10 ? "SAT" : (result == 20 ? "UNSAT" : "UNKNOWN")) << "\n";
	cout << "Solutions    : " << sol_count << "\n";
	cout << "Solving time : " << solve_elapsed << "s\n";

	fclose(fp);
	return sol_count;
}

// ---------------------------------------------------------------
// Main
// ---------------------------------------------------------------

int main(int argc, char* argv[]) {
	if (argc < 3) {
		cerr << "Usage: " << argv[0] << " <solution_path> <template_id>\n";
		return 1;
	}

	string solution_path = argv[1];
	int template_id      = atoi(argv[2]) + 1; // match Python: template_id = int(sys.argv[2]) + 1

	cout << "=== all_candidate_encoding for template " << (template_id - 1) << " ===\n";

	string parent_dir = "../";
	string cand_2_path = parent_dir + "refinements and candidate lines/2-candidate_lines/" + to_string(template_id) + "-candidate_lines.txt";
	string cand_3_path = parent_dir + "refinements and candidate lines/3-candidate_lines/" + to_string(template_id) + "-candidate_lines.txt";

	// ---- Load candidate lines ----
	auto t0 = chrono::steady_clock::now();

	cout << "Loading candidate lines from: " << cand_2_path << "\n";
	tie(cand_masks_A, points_A, count_A) = load_candidate_lines_file(cand_2_path);

	cout << "Loading candidate lines from: " << cand_3_path << "\n";
	tie(cand_masks_B, points_B, count_B) = load_candidate_lines_file(cand_3_path);

	total_points = points_A;
	total_points.insert(points_B.begin(), points_B.end());

	cout << "A candidates: " << count_A << " lines over " << points_A.size() << " points\n";
	cout << "B candidates: " << count_B << " lines over " << points_B.size() << " points\n";
	cout << "Total points: " << total_points.size() << "\n";
	cout << "Load time: " << chrono::duration<double>(chrono::steady_clock::now() - t0).count() << "s\n";

	// ---- Precompute bitset tables and point maps ----
	cout << "Precomputing data structures...\n";
	precomputeDataStructures();

	// ---- Build SAT + solve ----
	long long sol_count = build_and_solve(solution_path, /*can_forget=*/true);

	// ---- Summary ----
	cout << "\n=== FINAL RESULTS FOR TEMPLATE " << (template_id - 1) << " ===\n";
	cout << "Total solutions found: " << sol_count << "\n";
	cout << "Output file: " << solution_path << "\n";

	// Clean up
	delete[] intersects_once_AB;
	delete[] overlaps_AA;
	delete[] overlaps_BB;

	return 0;
}