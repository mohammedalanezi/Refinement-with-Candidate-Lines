/* partial_solution_refinement.cpp (Refinement step)
 * 
 * Given ten candidate lines from square A, enumerates every square B orthogonal to A and refines same template then writes the (A,B) pairs to solutions_<ID>.bin
 * 
 * A candidate line is a transversal (one cell per row and column) lying inside one template region. A refining square is ten disjoint candidate lines, one per symbol. 
 * B is orthogonal to A iff every B line meets every A line exactly once, so B is an exact cover of the 100 cells by B lines that pass that filter.
 * 
 * Cells are flat points p = r*order + c; bit p of a __uint128_t mask is cell p.
 * 
 * Must be included after cadical.hpp and exhaustive.hpp.
 * =============================================================================
 */
#include <iostream>
#include <fstream>
#include <vector>
#include <unordered_map>
#include <string>
#include <cstring>
#include <cstdio>
#include <tuple>
#include <chrono>
#include <array>
#include <algorithm>
#include <csignal>

// Collect wall-time statistics for the refinement phases
#ifndef TRACK_TIME
#define TRACK_TIME 1
#endif

// Write the (A,B) pairs to solutions_<ID>.bin
#ifndef WRITE_REFINEMENTS
#define WRITE_REFINEMENTS 1
#endif

// Write one DRAT proof per real cube solve to proofs_<ID>.drat.blob
#ifndef WRITE_PROOFS
#define WRITE_PROOFS 1
#endif

// How the compatible B lines are turned into exact covers:
//   0 -- custom branch-and-bound search (count_exact_covers)
//   1 -- SAT instance enumerated with ExhaustiveSearch (sat_count_exact_covers)
// Both modes append the same covers, sorted by line index, so their results and timings are directly comparable.
#ifndef SATREFINEMENT
#define SATREFINEMENT 0
#endif

// Log of automorphism-justified blocks, dynamic_clauses_<ID>.bin. The including program decides what is written to it.
#ifndef WRITE_DYNAMIC_CLAUSES
#define WRITE_DYNAMIC_CLAUSES 0
#endif

using namespace std;

#ifndef ORDER_DEFINED
#define ORDER_DEFINED
const int order = 10;
#endif

auto start_time = chrono::steady_clock::now();

// Row i (an A line) is a bitset over the B lines that meet A line i exactly once; rows_B is the row width in 64-bit words.
uint64_t* intersects_once_BA = nullptr;
int rows_B = 0;
uint64_t last_word_mask = 0; // valid bits of the last word of a row

long skipped_partial_solutions = 0; // A's with no possible B
long partial_count = 0;             // A's handed to processLine()
long total_refinements = 0;         // (A,B) pairs found (after the pair filter)
int count_A = 0;
int count_B = 0;

__uint128_t all_points_mask;

vector<__uint128_t> cand_masks_A;
vector<__uint128_t> cand_masks_B;

string output_path;
std::ofstream outfile;
std::ofstream dynamic_clauses_file;
string dynamic_clauses_path;

static int* intersecting_B_buf = nullptr;

// Optional pair-level symmetry filter, returns true to keep a pair. The SAT front-end only sees A, together with an arbitrary B witness, so symmetries
// that move A into B, or fix A and move B, can only be applied here where a real (A,B) pair exists. Null keeps every pair.
bool (*g_pair_filter)(const uint8_t A[100], const uint8_t B[100]) = nullptr;
long long g_pair_filter_examined = 0;

static inline int ctz128(__uint128_t x) {
	uint64_t lo = (uint64_t)x;
	return lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll((uint64_t)(x >> 64));
}

// Expands ten transversal masks into a flat 10x10 symbol grid (line s gets symbol s).
static inline void linesToGrid(const int line_idx[10], const vector<__uint128_t>& masks, uint8_t grid[100]) {
	for (int s = 0; s < 10; ++s) {
		__uint128_t m = masks[line_idx[s]];
		while (m) {
			int p = ctz128(m);
			grid[p] = (uint8_t)s;
			m &= m - 1;
		}
	}
}

// Set around throwaway solves (cube-tuning probes) so that solve_partial_solution() writes nothing and leaves total_refinements and
// skipped_partial_solutions untouched. partial_count is still bumped by processLine(); the caller must restore it.
bool g_test_mode = false;

// ---------------------------------------------------------------------------
// Graceful SIGINT/SIGTERM handling.
//
// The handler only sets a flag, which is all that is async-signal-safe. The flag is polled by SignalTerminator (CaDiCaL checks it between its own decisions, never inside a propagator callback) 
// and by the driver's cube loop between cubes. A record being written when the signal arrives is therefore always completed, so solutions_<ID>.bin never ends in a truncated record.
// ---------------------------------------------------------------------------
volatile std::sig_atomic_t g_stop_requested = 0;
volatile std::sig_atomic_t g_stop_signal    = 0;

extern "C" void request_stop(int sig) {
	g_stop_requested = 1;
	g_stop_signal    = sig;
}

void install_stop_handler() {
	std::signal(SIGINT,  request_stop);
	std::signal(SIGTERM, request_stop);
}

// Exit code for the shell: 128 + signal number if interrupted, else 0.
int stop_exit_code() {
	return g_stop_requested ? (128 + (int)g_stop_signal) : 0;
}

struct SignalTerminator : public CaDiCaL::Terminator {
	bool terminate() override { return g_stop_requested != 0; }
};
SignalTerminator g_signal_terminator;

// Frequency squares of the two "trivial" incidence bits (row < 4, column < 4) that complete the four-bit weight used by the candidate-line encoding.
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
double total_refinement_early_blocking = 0.0;
double total_refinement_solve_time = 0.0;
#if SATREFINEMENT == 1
double total_refinement_sat_encode_time = 0.0;
#endif
#endif

#if SATREFINEMENT == 1
long long total_refinement_sat_calls   = 0; // cover instances handed to the SAT solver
long long total_refinement_sat_vars    = 0; // line variables summed over those instances
long long total_refinement_sat_clauses = 0; // clauses summed over those instances
#endif

struct U128Hash {
	size_t operator()(__uint128_t v) const {
		uint64_t lo = (uint64_t)v;
		uint64_t hi = (uint64_t)(v >> 64);
		// MurmurHash-style finalizer
		lo ^= lo >> 33;
		lo *= 0xff51afd7ed558ccdULL;
		lo ^= lo >> 33;

		hi ^= hi >> 33;
		hi *= 0xc4ceb9fe1a85ec53ULL;
		hi ^= hi >> 33;
		return lo ^ (hi * 0x9e3779b97f4a7c15ULL);
	}
};

// Mask of an A candidate line -> its index in cand_masks_A.
unordered_map<__uint128_t, int, U128Hash> cand_hash_A;

/** Builds a mask from 1-based point numbers in [1, 100]; point x sets bit x-1. */
__uint128_t make_mask(const vector<int>& line) {
	__uint128_t m = 0;
	for (int x : line)
		m |= ((__uint128_t)1 << (x - 1));
	return m;
}

/** True iff the two masks share exactly one bit. */
bool intersectsExactlyOnce(__uint128_t m1, __uint128_t m2) {
	__uint128_t c = m1 & m2;
	return c != 0 && (c & (c - 1)) == 0;
}

// ---------------------------------------------------------------------------
// Output files
// ---------------------------------------------------------------------------

/** Writes a 100-bit permutation mask (one bit per row and column) as 5 bytes: the column of each row as a nibble, low nibble first. */
void write_compact_line(std::ofstream &out, __uint128_t mask) {
	uint8_t buf[5] = {0};

	for (int row = 0; row < 10; ++row) {
		uint16_t row_bits = (mask >> (row * 10)) & 0x3FF;
		int col = __builtin_ctz(row_bits);

		int byte_idx = row / 2;
		if (row % 2 == 0)
			buf[byte_idx] = col;
		else
			buf[byte_idx] |= (col << 4);
	}

	out.write(reinterpret_cast<const char*>(buf), 5);
}

/** Writes the 0xFF byte that starts each solutions record: 10 A lines, then 10 lines per B cover. */
void write_separator(std::ofstream &out) {
	uint8_t sep = 0xFF;
	out.write(reinterpret_cast<const char*>(&sep), 1);
}

void flush_output() {
	outfile.flush();
	if (dynamic_clauses_file.is_open()) dynamic_clauses_file.flush();
}

/** Opens <path>/dynamic_clauses_<ID>.bin. Returns false on failure. */
bool open_dynamic_clauses(const string& path, const string& ID) {
	dynamic_clauses_path = path + "/dynamic_clauses_" + ID + ".bin";
	dynamic_clauses_file.open(dynamic_clauses_path, std::ios::binary | std::ios::out | std::ios::trunc);
	if (!dynamic_clauses_file) {
		std::cerr << "Cannot open '" << dynamic_clauses_path << "' for writing\n";
		return false;
	}
	return true;
}

void close_dynamic_clauses() {
	if (dynamic_clauses_file.is_open()) dynamic_clauses_file.close();
}

// ---------------------------------------------------------------------------
// Per-cube DRAT proof blob.
//
// Every real cube solve appends one proof to a single file, proofs_<ID>.drat.blob, instead of creating one file per cube. Record layout:
//
//   [4 bytes cube_index, little-endian]
//   [8 bytes proof_len,  little-endian]   -- length of the DRAT data that follows
//   [proof_len bytes]                     -- binary DRAT proof streamed out of CaDiCaL
//
// proof_len is unknown until solve() returns, so begin_cube_proof_record() reserves the field and end_cube_proof_record() patches it. 
// The length prefix is needed because binary DRAT can contain any byte pattern, so no separator byte is safe.
// ---------------------------------------------------------------------------
std::FILE* g_proof_blob_fp = nullptr;
string proof_blob_path;

bool open_proof_blob(const string& path, const string& ID) {
	proof_blob_path = path + "/proofs_" + ID + ".drat.blob";
	g_proof_blob_fp = std::fopen(proof_blob_path.c_str(), "wb");
	if (!g_proof_blob_fp) {
		std::cerr << "Cannot open 'proofs_" + ID + ".drat.blob' for writing\n";
		return false;
	}
	return true;
}

/** Safe to call even if the blob was never opened. */
void close_proof_blob() {
	if (g_proof_blob_fp) {
		std::fclose(g_proof_blob_fp);
		g_proof_blob_fp = nullptr;
	}
}

/**
 * Starts one cube's proof record and attaches CaDiCaL's DRAT tracer to the blob. Call on a freshly copied solver, before the cube's unit clauses are added, so the whole solve is traced.
 *
 * @param proof_start_pos Output: file offset where the proof bytes begin.
 * @returns File offset of the length field, to be passed to end_cube_proof_record().
 */
long long begin_cube_proof_record(CaDiCaL::Solver& solver, uint32_t cube_index, long long& proof_start_pos) {
	std::fwrite(&cube_index, sizeof(cube_index), 1, g_proof_blob_fp);

	long long length_field_pos = std::ftell(g_proof_blob_fp);
	uint64_t placeholder = 0;
	std::fwrite(&placeholder, sizeof(placeholder), 1, g_proof_blob_fp);
	proof_start_pos = std::ftell(g_proof_blob_fp);

	solver.trace_proof(g_proof_blob_fp, "cube_proof"); // CaDiCaL does not close a FILE* it was handed

	return length_field_pos;
}

/** Detaches the tracer, patches the real proof length into the record and returns the cursor to the end of the blob. */
void end_cube_proof_record(CaDiCaL::Solver& solver, long long length_field_pos, long long proof_start_pos) {
	solver.flush_proof_trace();
	solver.close_proof_trace(false); // false: detach without printing CaDiCaL's proof stats

	long long proof_end_pos = std::ftell(g_proof_blob_fp);
	uint64_t proof_len = (uint64_t)(proof_end_pos - proof_start_pos);

	std::fseek(g_proof_blob_fp, length_field_pos, SEEK_SET);
	std::fwrite(&proof_len, sizeof(proof_len), 1, g_proof_blob_fp);
	std::fseek(g_proof_blob_fp, proof_end_pos, SEEK_SET);

	std::fflush(g_proof_blob_fp); // a signal between cubes must not lose a finished proof
}

// ---------------------------------------------------------------------------
// Candidate-line discovery
// ---------------------------------------------------------------------------

// Collects every model of a candidate-line instance as a mask; is_A selects the destination.
struct CandidatePolicy {
	mutable bool is_A = false;
	explicit operator bool() const { return true; }
	bool operator()(const std::vector<int>& solution) const {
		if (is_A)
			cand_masks_A.push_back(make_mask(solution));
		else
			cand_masks_B.push_back(make_mask(solution));
		return true;
	}
	static constexpr bool notifyAssignment = false;
	static constexpr bool earlyClause = false;
	static constexpr bool minimizeClause = false;
};

/**
 * Sequential-counter encoding of "between min_val and max_val of var_list are true" (Sinz). Allocates auxiliary variables starting at var_cnt + 1 and updates var_cnt.
 */
static void addCardinalityClauses(CaDiCaL::Solver &solver, const std::vector<int> &var_list, int min_val, int max_val, int &var_cnt) {
	int n = (int)var_list.size();
	int k = max_val + 1;   // s[i][k] is forbidden (at most max_val)
	int l = min_val;       // s[n][1..l] are forced (at least min_val)

	// s[i][j]: at least j of x_1..x_i are true
	int num_aux = (n + 1) * (k + 1);
	int need_max = var_cnt + num_aux;
	solver.resize(need_max);

	std::vector<std::vector<int>> s(n + 1, std::vector<int>(k + 1));
	for (int i = 0; i <= n; ++i)
		for (int j = 0; j <= k; ++j)
			s[i][j] = ++var_cnt;

	// at least 0 of any prefix is true
	for (int i = 0; i <= n; ++i) {
		solver.add(s[i][0]);
		solver.add(0);
	}

	// at least j >= 1 of the empty prefix is false
	for (int j = 1; j <= k; ++j) {
		solver.add(-s[0][j]);
		solver.add(0);
	}

	// lower bound
	for (int j = 1; j <= l; ++j) {
		solver.add(s[n][j]);
		solver.add(0);
	}

	// upper bound
	for (int i = 1; i <= n; ++i) {
		solver.add(-s[i][k]);
		solver.add(0);
	}

	// counter propagation
	for (int i = 1; i <= n; ++i)
		for (int j = 1; j <= k; ++j) {
			// s[i-1][j] -> s[i][j]
			solver.add(-s[i-1][j]);
			solver.add(s[i][j]);
			solver.add(0);

			// x_i and s[i-1][j-1] -> s[i][j]
			solver.add(-var_list[i-1]);
			solver.add(-s[i-1][j-1]);
			solver.add(s[i][j]);
			solver.add(0);

			if (j <= l) {
				// s[i][j] -> s[i-1][j] or x_i
				solver.add(-s[i][j]);
				solver.add(s[i-1][j]);
				solver.add(var_list[i-1]);
				solver.add(0);

				// s[i][j] -> s[i-1][j-1]
				solver.add(-s[i][j]);
				solver.add(s[i-1][j-1]);
				solver.add(0);
			}
		}
}

// Bits 0 and 1 are the trivial incidence squares, bits 2 and 3 the two template squares.
static int getTemplateBit(const vector<vector<vector<int>>>& tmpl, int r, int c, int bit) {
	if (bit >= 2)
		return tmpl[bit - 2][r][c];
	else
		return trivialTemplate[bit][r][c];
}

/**
 * Encodes the candidate lines of one square as a SAT instance over 100 variables (variable r*order + c + 1 = line passes through cell (r,c)).
 * A line is a transversal that stays inside one region of the frequency square:
 *   relational:     the cells where it is 1, using exactly one cell of weight 4 and nine of weight 2
 *   non-relational: the cells where it is 0, using exactly six cells of weight 2 and four of weight 0
 * where a cell's weight is the number of ones among its four bits (row < 4, column < 4, both template squares).
 */
static void createCandidateEncoding(CaDiCaL::Solver &solver, const vector<vector<vector<int>>>& tmpl, bool isRelational, int frequencySquare) {
	solver.declare_more_variables(100);
	int variable_count = 100;
	int number_bits = tmpl.size() + trivialTemplate.size();

	// one cell per row and per column
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

	for(int r = 0; r < order; r++)
		for(int c = 0; c < order; c++) {
			int weight = 0;
			for(int i = 0; i < number_bits; i++)
				weight += getTemplateBit(tmpl, r, c, i);

			// cells of the wrong region are excluded, the others are bucketed by weight
			int inRegion = getTemplateBit(tmpl, r, c, frequencySquare);
			if (inRegion == (isRelational ? 1 : 0))
				weightBuckets[weight].push_back(r * order + c + 1);
			else
				solver.clause(-(r * order + c + 1));
		}

	if(isRelational) {
		if (weightBuckets[4].size() > 0)
			addCardinalityClauses(solver, weightBuckets[4], 1, 1, variable_count);
		if (weightBuckets[2].size() > 0)
			addCardinalityClauses(solver, weightBuckets[2], 9, 9, variable_count);
	} else {
		if (weightBuckets[2].size() > 0)
			addCardinalityClauses(solver, weightBuckets[2], 6, 6, variable_count);
		if (weightBuckets[0].size() > 0)
			addCardinalityClauses(solver, weightBuckets[0], 4, 4, variable_count);
	}
}

/** Enumerates the relational and non-relational candidate lines of square A (isA) or B, appending them to cand_masks_A / cand_masks_B. */
void find_candidate_lines(const vector<vector<vector<int>>>& tmpl, const bool isA) {
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

	int frequencySquare = isA ? 2 : 3;
	createCandidateEncoding(relationalCandidateSolver, tmpl, true, frequencySquare);
	createCandidateEncoding(nonRelationalCandidateSolver, tmpl, false, frequencySquare);

	CandidatePolicy candidatePolicy;
	candidatePolicy.is_A = isA;

	ExhaustiveSearch<CandidatePolicy> relationalCandidatePropagator(&relationalCandidateSolver, candidateOptions, candidatePolicy);
	ExhaustiveSearch<CandidatePolicy> nonRelationalCandidatePropagator(&nonRelationalCandidateSolver, candidateOptions, candidatePolicy);

	relationalCandidateSolver.solve();
	nonRelationalCandidateSolver.solve();

	if(isA)
		count_A = cand_masks_A.size();
	else
		count_B = cand_masks_B.size();

	cout << "\t\tFound " << (isA ? count_A : count_B) << " candidate lines for square " << (isA ? "A" : "B");

#if TRACK_TIME == 1
	cout << " in " << chrono::duration<double>(chrono::steady_clock::now() - timer).count() << "s\n";
#else
	cout << "\n";
#endif
}

/**
 * Precomputes the tables used per A:
 *  - intersects_once_BA: row i is the bitset of B lines meeting A line i exactly once (see the declaration).
 *  - cand_hash_A: A line mask -> index.
 *  - intersecting_B_buf and last_word_mask, the scratch buffer and tail mask used when filtering B lines.
 */
void precomputeDataStructures() {
	auto start = chrono::steady_clock::now();

	all_points_mask = ((__uint128_t)1 << 100) - 1;

	rows_B = (count_B + 63) / 64;
	intersects_once_BA = new uint64_t[(long long)count_A * rows_B]();

	for (int i = 0; i < count_A; ++i)
		for (int j = 0; j < count_B; ++j)
			if (intersectsExactlyOnce(cand_masks_A[i], cand_masks_B[j]))
				intersects_once_BA[(long long)i * rows_B + j / 64] |= (1ULL << (j % 64));

	cand_hash_A.reserve(count_A * 2);
	for (int i = 0; i < count_A; ++i)
		cand_hash_A[cand_masks_A[i]] = i;

	intersecting_B_buf = new int[count_B];

	int last_word_bits = count_B % 64;
	last_word_mask = last_word_bits ? (1ULL << last_word_bits) - 1 : ~0ULL;

	double elapsed = chrono::duration<double>(chrono::steady_clock::now() - start).count();
	cout << "\tPrecomputed intersections using masks in " << elapsed << " seconds." << endl;
}

// ---------------------------------------------------------------------------
// B lines and exact covers
// ---------------------------------------------------------------------------

/**
 * Collects the B lines that meet every given A line exactly once: the AND of the corresponding intersects_once_BA rows.
 *
 * @param intersecting_indices Output: surviving B line indices in ascending order; needs room for count_B entries.
 * @param intersection_count   Output: number of indices written (the caller passes 0). Set to 0 if the AND becomes empty.
 * @param opposite_indices     The ten A line indices; negative entries are skipped.
 * @param union_mask           Output: OR of the masks of the surviving lines (left untouched if there are none).
 */
void getIntersectingBLineIndices(int intersecting_indices[], int& intersection_count, const int opposite_indices[], __uint128_t& union_mask) {
	const int words = rows_B;

	uint64_t* result = (uint64_t*)alloca(words * sizeof(uint64_t));
	bool resultSet = false;

	for (int j = 0; j < order; j++)
		if (opposite_indices[j] >= 0) {
			const uint64_t* row = intersects_once_BA + (long long)opposite_indices[j] * words;
			if (!resultSet) {
				resultSet = true;
				memcpy(result, row, words * sizeof(uint64_t));
				continue;
			}
			uint64_t nonzero = 0;
			for (int w = 0; w < words; ++w) {
				result[w] &= row[w];
				nonzero |= result[w];
			}
			if (!nonzero) { // nothing can survive any more
				intersection_count = 0;
				return;
			}
		}
	if (!resultSet) return;

	result[words - 1] &= last_word_mask;
	for (int w = 0; w < words; ++w) {
		uint64_t word = result[w];
		while (word) {
			int idx = w * 64 + __builtin_ctzll(word);
			intersecting_indices[intersection_count++] = idx;
			union_mask |= cand_masks_B[idx];
			word &= word - 1;
		}
	}
}

#if SATREFINEMENT == 0
/**
 * Recursively enumerates the exact covers of all 100 cells by the B lines B_indices[idx..B_count-1], on top of the lines already chosen.
 * At each line it either skips it or, if it does not overlap `covered`, includes it. Every line covers exactly `order` cells, so a disjoint set
 * covering all 100 cells has exactly `order` lines and no separate count is needed.
 *
 * Pruning: (1) the remaining lines together cannot cover the missing cells; (2) too few lines remain to reach `order`.
 *
 * @param covered Cells covered by the lines chosen so far.
 * @param idx     Next candidate to consider.
 * @param chosen  Number of lines chosen so far.
 * @param suffix  suffix[i] is the OR of the masks of B_indices[i..B_count-1]; length B_count + 1 with suffix[B_count] == 0.
 * @param path    Scratch buffer holding the chosen line indices.
 * @param found   Output: one entry per complete cover.
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

	if ((covered | suffix[idx]) != all_points_mask) return;
	if (chosen + (B_count - idx) < order) return;

	// skip line idx
	count_exact_covers(B_indices, B_count, covered, idx + 1, chosen, suffix, path, found);

	// include line idx
	__uint128_t m = cand_masks_B[B_indices[idx]];
	if ((m & covered) == 0) {
		path[chosen] = B_indices[idx];
		count_exact_covers(B_indices, B_count, covered | m, idx + 1, chosen + 1, suffix, path, found);
	}
}
#endif // SATREFINEMENT == 0

#if SATREFINEMENT == 1
/**
 * Collects one exact cover per model of instance built by sat_count_exact_covers(). Every variable of instance is observed, so blocking as soon as all assigned is sound (see exhaustive.hpp).
 *
 * pos_vars lists selected line variables in ascending order, which is also ascending order of B_indices, so cover comes out sorted; it is sorted
 * again anyway so symbol labelling of B matches the custom search exactly.
 */
struct ExactCoverPolicy {
	vector<array<int, order>>* found = nullptr;
	const int* B_indices = nullptr;

	explicit operator bool() const { return true; }

	bool operator()(const std::vector<int>& pos_vars) const {
		if ((int)pos_vars.size() != order) // exactly-one per cell forces `order` lines; anything else is not a cover
			return true;

		array<int, order> cover;
		for (int i = 0; i < order; ++i)
			cover[i] = B_indices[pos_vars[i] - 1];
		std::sort(cover.begin(), cover.end());
		found->push_back(cover);
		return true;
	}

	static constexpr bool notifyAssignment = false;
	static constexpr bool earlyClause      = false;
	static constexpr bool minimizeClause   = false;
};

/**
 * SAT version of count_exact_covers(). Variable i+1 means "line B_indices[i] is used"; for every cell exactly one of the lines through it is used.
 *
 * @param B_indices Ascending indices into cand_masks_B of the lines that survived filtering.
 * @returns Number of covers found; each is appended to `found`.
 */
static int sat_count_exact_covers(const int B_indices[], int B_count, vector<array<int, order>>& found) {
#if TRACK_TIME == 1
	auto encode_timer = chrono::steady_clock::now();
#endif

	CaDiCaL::Solver cover_solver;
	cover_solver.set("check",        1);
	cover_solver.set("checkproof",   1);
	cover_solver.set("report",       0);
	cover_solver.set("inprocessing", 0);
	cover_solver.set("factor",       0);
	cover_solver.set("factorcheck",  0);
	cover_solver.declare_more_variables(B_count);

	// lines through each cell; static so the buckets keep their capacity between calls
	static thread_local vector<vector<int>> point_lines(order * order);
	for (auto& bucket : point_lines)
		bucket.clear();

	for (int i = 0; i < B_count; ++i) {
		__uint128_t m = cand_masks_B[B_indices[i]];
		while (m) {
			point_lines[ctz128(m)].push_back(i + 1);
			m &= m - 1;
		}
	}

	long long clause_count = 0;
	for (int p = 0; p < order * order; ++p) {
		const vector<int>& lines = point_lines[p];
		if (lines.empty()) // cell not covered by any line: no cover exists
			return 0;

		cover_solver.clause(lines); // at least one line through p
		++clause_count;

		for (size_t a = 0; a + 1 < lines.size(); ++a) // at most one line through p
			for (size_t b = a + 1; b < lines.size(); ++b) {
				cover_solver.clause({-lines[a], -lines[b]});
				++clause_count;
			}
	}

	static thread_local vector<int> cover_observe;
	cover_observe.resize(B_count);
	for (int i = 0; i < B_count; ++i)
		cover_observe[i] = i + 1;

	ExhaustiveSearchOptions cover_options;
	cover_options.to_observe = cover_observe;
	cover_options.only_neg   = true;
	cover_options.can_forget = true;

	ExactCoverPolicy cover_policy;
	cover_policy.found      = &found;
	cover_policy.B_indices  = B_indices;

	ExhaustiveSearch<ExactCoverPolicy> cover_propagator(&cover_solver, cover_options, cover_policy);

	total_refinement_sat_calls   += 1;
	total_refinement_sat_vars    += B_count;
	total_refinement_sat_clauses += clause_count;

#if TRACK_TIME == 1
	total_refinement_sat_encode_time += chrono::duration<double>(chrono::steady_clock::now() - encode_timer).count();
#endif

	cover_solver.solve();

	return (int)cover_propagator.get_solution_count();
}
#endif // SATREFINEMENT == 1

/**
 * Enumerates the exact covers of the 100 cells by the filtered B lines.
 * @param union_B OR of the masks of all lines in B_indices.
 * @returns The number of covers appended to `found`, or -1 if the lines cannot cover every cell.
 */
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
		// `order` lines covering all cells must be disjoint, so this is the only cover (no search needed in either mode).
		array<int, order> cover;
		for (int i = 0; i < order; ++i) cover[i] = B_indices[i];
		found.push_back(cover);
		return 1;
	}

#if SATREFINEMENT == 1
	int sol_count = sat_count_exact_covers(B_indices, B_count, found);
#else
	__uint128_t suffix[B_count + 1];
	suffix[B_count] = 0;
	for (int i = B_count - 1; i >= 0; --i)
		suffix[i] = suffix[i + 1] | cand_masks_B[B_indices[i]];

	int path[order];
	count_exact_covers(B_indices, B_count, 0, 0, 0, suffix, path, found);
	int sol_count = (int)found.size();
#endif

#if TRACK_TIME == 1
	total_refinement_solve_time += chrono::duration<double>(chrono::steady_clock::now() - timer).count();
#endif

	return sol_count;
}

/** Filters the B lines against the ten A lines and enumerates the covers. Returns -1 if no cover is possible, else the number found. */
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

/**
 * Finds every B for the A given by ten candidate-line indices (one per symbol), applies the pair filter and writes the surviving pairs.
 * @returns false if at least one pair was recorded, true otherwise.
 */
bool solve_partial_solution(const int sym_A_idx[order]) {
	static thread_local vector<array<int, order>> found_B_refinements;
	found_B_refinements.clear();

	long int refinement_count = processLine(sym_A_idx, found_B_refinements);
	if (g_test_mode) return true;

	if (refinement_count < 0) {
		skipped_partial_solutions += 1;
		return true;
	}
	if (refinement_count == 0) return true;

	// Pair-level symmetry filter. This is the first point at which a genuine (A,B) pair exists.
	if (g_pair_filter) {
		uint8_t A[100], B[100];
		linesToGrid(sym_A_idx, cand_masks_A, A);

		size_t keep = 0;
		for (size_t k = 0; k < found_B_refinements.size(); ++k) {
			linesToGrid(found_B_refinements[k].data(), cand_masks_B, B);
			++g_pair_filter_examined;
			if (g_pair_filter(A, B))
				found_B_refinements[keep++] = found_B_refinements[k];
		}
		found_B_refinements.resize(keep);
		refinement_count = (long int)keep;
		if (refinement_count == 0) return true;
	}

	total_refinements += refinement_count;
#if WRITE_REFINEMENTS == 1
	write_separator(outfile);
	for (int i = 0; i < order; ++i)
		write_compact_line(outfile, cand_masks_A[sym_A_idx[i]]);

	for (const auto& cover : found_B_refinements)
		for (int i = 0; i < order; ++i)
			write_compact_line(outfile, cand_masks_B[cover[i]]);
#endif
	return false;
}

/**
 * Opens the output files, finds the candidate lines of both squares and precomputes the tables.
 * @param tmpl The two binary frequency squares.
 * @returns 0 on success, 1 if an output file cannot be opened.
 */
int setup(const vector<vector<vector<int>>>& tmpl, string path, string ID) {
	output_path = path;
#if WRITE_REFINEMENTS == 1
	outfile.exceptions(std::ios::failbit | std::ios::badbit);
	outfile.open(output_path + "/solutions_" + ID + ".bin", std::ios::binary | std::ios::out);
	if (!outfile) {
		std::cerr << "Cannot open 'solutions_" + ID + ".bin' for writing\n";
		return 1;
	}
#endif

#if WRITE_DYNAMIC_CLAUSES == 1
	if (!open_dynamic_clauses(output_path, ID))
		return 1;
#endif

#if WRITE_PROOFS == 1
	if (!open_proof_blob(output_path, ID))
		return 1;
#endif

	ios::sync_with_stdio(false);
	cin.tie(nullptr);

	cout << "\tFinding candidate lines from template..." << endl;
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