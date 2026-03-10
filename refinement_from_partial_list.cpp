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
#define MAX_RUNTIME 0 // a value below or equal to 0 skips timeout

using namespace std;

// Global data structures
const int order = 10;

unordered_set<int> points_A;
unordered_set<int> points_B;
unordered_set<int> total_points;

int* intersections_AB = nullptr; // flat row-major array: intersections_AB[i * count_B + j] = number of intersections between cand_masks_A[i] and cand_masks_B[j]
int* all_line_indices_A = nullptr;
int* all_line_indices_B = nullptr;

long partial_count = 0;
int count_A = 0;
int count_B = 0;

#if TRACK_TIME == 1 // This tracking probably doesn't work the best when we are multithreading, TODO: fix that
double total_sat_solving_time = 0.0; // wall time
double total_sat_encoding_time = 0.0;
double total_sat_covering_time = 0.0;
double total_sat_intersection_time = 0.0;
double total_sat_setup_time = 0.0;

double total_line_read_time = 0.0;
double total_line_finding_time = 0.0;
double total_line_parallel_time = 0.0;
double total_line_intersection_time = 0.0;
#endif

struct Mask {
    uint64_t lo = 0; // bits 0–63
    uint64_t hi = 0; // bits 64–127
	
    bool operator==(const Mask& other) const {
        return (lo == other.lo && hi == other.hi);
    }
	
    void print() const {
		for (int i = 63; i >= 0; --i) {
			std::cout << ((hi >> i) & 1);
			if (i % 8 == 0 && i > 0) cout << " ";
		}
		for (int i = 63; i >= 0; --i) {
			std::cout << ((lo >> i) & 1);
			if (i % 8 == 0 && i > 0) cout << " ";
		}
		cout << endl;
    }
	
	bool isSet(int p) const {
		if (p < 0 || p > 127) 
			return false; // bounds check
		if (p < 64) {
			return (lo >> p) & 1ULL;
		} else {
			return (hi >> (p - 64)) & 1ULL;
		}
	}
};
// replace all vectors to masks (exclduing incidies)
// replace vectors with arrays whenever possible, base it on order value

vector<Mask> cand_masks_A;
vector<Mask> cand_masks_B;

Mask make_mask(const vector<int>& line) {
    Mask m;
    for (int x : line) {
        int idx = x - 1; // convert 1-100 to 0-99
        if (idx < 64)
            m.lo |= (1ULL << idx);
        else
            m.hi |= (1ULL << (idx - 64));
    }
    return m;
}

Mask make_mask(const int* line) {
    Mask m;
	for(int i = 0; i < order; i++) {
		int x = line[i];
        int idx = x - 1; // convert 1-100 to 0-99
        if (idx < 64)
            m.lo |= (1ULL << idx);
        else
            m.hi |= (1ULL << (idx - 64));
    }
    return m;
}

int computeIntersectionCountMask(const Mask& m1, const Mask& m2) { // compute intersection count between two masks
    return __builtin_popcountll(m1.lo & m2.lo) + __builtin_popcountll(m1.hi & m2.hi);
}

int getLowestSetBit(const Mask& m)
{
	if(m.lo > 0)
		return __builtin_ctzll(m.lo);
	else
		return __builtin_ctzll(m.hi) + 64;
}

void clearLowestSetBit(Mask& m)
{
	if(m.lo > 0)
		m.lo &= m.lo - 1;
	else
		m.hi &= m.hi - 1;
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

tuple<vector<Mask>, unordered_set<int>, int> load_candidate_lines_file(const string& path) {
	ifstream f(path);
	vector<Mask> lines;
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

int get1DIndex(int r, int c) {
	return r * order + c + 1;
}

void solutionToCandidateLines(const int* solution, const int& solution_count, Mask a_lines[], int& a_solutions, Mask b_lines[], int& b_solutions) {
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

void findLineIndices(int solution_indices[], Mask solution_lines[], const int line_count, const vector<Mask>& candidate_masks) {
    for (int i = 0; i < line_count; i++) // find matching candidate line
        for (size_t j = 0; j < candidate_masks.size(); ++j)
            if (candidate_masks[j] == solution_lines[i]) {
                solution_indices[i] = j;
                break;
            }
}

void precomputeDataStructures() {
    auto start = chrono::steady_clock::now();
    
    intersections_AB = new int[count_A * count_B];
    for (int i = 0; i < count_A; ++i)
        for (int j = 0; j < count_B; ++j)
            intersections_AB[i * count_B + j] = computeIntersectionCountMask(cand_masks_A[i], cand_masks_B[j]);

	all_line_indices_A = new int[count_A];
	for(int i = 0; i < count_A; i++)
		all_line_indices_A[i] = i;

	all_line_indices_B = new int[count_B];
	for(int i = 0; i < count_B; i++)
		all_line_indices_B[i] = i;
    
    auto end = chrono::steady_clock::now();
    double elapsed = chrono::duration<double>(end - start).count();
    cout << "Precomputed intersections using masks in " << elapsed << " seconds." << endl;
    //cout << "  A-B: " << cand_lines_A.size() << "x" << cand_lines_B.size() << " = " << (cand_lines_A.size() * cand_lines_B.size()) << " entries" << endl;
}

void getAllParallelLineIndices(int*& parallel_indices, int& parallel_count, const int line_indices[], const int line_count, bool is_A) {
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

    Mask total_incidence = masks[line_indices[0]];
	for(int i=1; i < line_count; i++) { // get all points contained in line indices
		total_incidence.lo |= masks[line_indices[i]].lo;
		total_incidence.hi |= masks[line_indices[i]].hi;
	}

    for (size_t i = 0; i < masks.size(); i++)
		if(computeIntersectionCountMask(masks[i], total_incidence) == 0)
			parallel_indices[parallel_count++] = i;
}


void getIntersectingLineIndices(int intersecting_indices[], int& intersection_count, const int line_indices[], const int line_count, const int opposite_indices[], const int opposite_count, int intersections, bool is_A) {
    for (int i = 0; i < line_count; i++) {
		int line_idx = line_indices[i];
        bool valid = true;
        
        for (int j = 0; j < opposite_count; j++) { // VECTOR
			int opp_idx = opposite_indices[j];
            int inter = is_A ? intersections_AB[line_idx * count_B + opp_idx] : intersections_AB[opp_idx * count_B + line_idx];
            if (inter != intersections) {
                valid = false;
                break;
            }
        }
        
        if (valid) 
            intersecting_indices[intersection_count++] = line_idx;
    }
}

int get_refinements(const int& trans_A, const int& trans_B, const int A_indices[], const int A_count, const int B_indices[], const int B_count) {
#if TRACK_TIME == 1
    auto timer = chrono::steady_clock::now();
#endif
    
    vector<int> observed;
    CaDiCaL::Solver solver;

	int var_cnt = A_count + A_count;

	for(int i = 0; i < trans_A; i++)
		solver.clause(i+1);
	for(int i = 0; i < trans_B; i++)
		solver.clause(i+1+A_count);

#if TRACK_TIME == 1
    double setup_elapsed = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	timer = chrono::steady_clock::now();
#endif

	if(trans_A < order)
		for(int i = 0; i < A_count; i++)
			for(int j = i + 1; j < A_count; j++)
				if(computeIntersectionCountMask(cand_masks_A[A_indices[i]], cand_masks_A[A_indices[j]]) > 0)
					solver.clause(-(i + 1), -(j + 1));
					
	if(trans_B < order)
		for(int i = 0; i < B_count; i++)
			for(int j = i + 1; j < B_count; j++)
				if(computeIntersectionCountMask(cand_masks_B[B_indices[i]], cand_masks_B[B_indices[j]]) > 0)
					solver.clause(-(i + 1 + A_count), -(j + 1 + A_count));
    
    for (int p = 0; p < order*order; p++) { // go through all a's, check if a has pth position true, if so solver.add(i)
		for (size_t i = 0; i < A_count; i++) {
			const Mask& m = cand_masks_A[A_indices[i]]; 
			if(m.isSet(p))
				solver.add(i + 1);
		}
		solver.add(0);
	}
    for (int p = 0; p < order*order; p++) {
		for (size_t i = 0; i < B_count; i++) {
			const Mask& m = cand_masks_B[B_indices[i]]; 
			if(m.isSet(p))
				solver.add(i + 1 + A_count);
		}
		solver.add(0);
	}

#if TRACK_TIME == 1
    double covering_elapsed = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	timer = chrono::steady_clock::now();
#endif

    if(trans_A > 0 && trans_B > 0) {
        for (size_t i = 0; i < A_count; i++) {
            const int a_idx = A_indices[i];
            const int a_var = i + 1;
        	const int* intersection_row = intersections_AB + a_idx * count_B;
            
            for (size_t j = 0; j < B_count; j++) {
				int b_idx = B_indices[j]; 
				if (intersection_row[b_idx] != 1)
					solver.clause(-a_var, -(A_count + j + 1));
			}
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
	total_sat_covering_time += covering_elapsed;
	total_sat_intersection_time += intersections_elapsed;
	total_sat_solving_time += solver_elapsed;
	total_sat_encoding_time += covering_elapsed + intersections_elapsed + setup_elapsed;
#endif

    return sol_count;
}

// Modified to work with indices
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
#endif 

	Mask A_sol_lines[order];
	int trans_A = 0;
	Mask B_sol_lines[order];
	int trans_B = 0;

	solutionToCandidateLines(solution, solution_count, A_sol_lines, trans_A, B_sol_lines, trans_B);

#if TRACK_TIME == 1
	double elapsed_1 = chrono::duration<double>(chrono::steady_clock::now() - conversion_time).count();
	auto index_time = chrono::steady_clock::now();
#endif
	
	// Convert solution lines to their candidate line indices
	int A_sol_indices[trans_A];
	int B_sol_indices[trans_B];
	findLineIndices(A_sol_indices, A_sol_lines, trans_A, cand_masks_A);
	findLineIndices(B_sol_indices, B_sol_lines, trans_B, cand_masks_B);

#if TRACK_TIME == 1
	double elapsed_index = chrono::duration<double>(chrono::steady_clock::now() - index_time).count();
	auto parallel_time = chrono::steady_clock::now();
#endif

	int* parallel_A_indices = (int*)alloca(count_A * sizeof(int));
	int  parallel_A_count = 0;
	int* parallel_B_indices = (int*)alloca(count_B * sizeof(int));
	int  parallel_B_count = 0;

	getAllParallelLineIndices(parallel_A_indices, parallel_A_count, A_sol_indices, trans_A, true);
	getAllParallelLineIndices(parallel_B_indices, parallel_B_count, B_sol_indices, trans_B, false);

#if TRACK_TIME == 1
	double elapsed_2 = chrono::duration<double>(chrono::steady_clock::now() - parallel_time).count();
	auto intersection_time = chrono::steady_clock::now();
#endif

	// Filter to those that intersect exactly once with every line of the opposite square's solution using precomputed intersections
	int intersecting_A_indices[parallel_A_count];
	int intersection_A_count = 0;
	int intersecting_B_indices[parallel_B_count];
	int intersection_B_count = 0;

	getIntersectingLineIndices(intersecting_A_indices, intersection_A_count, parallel_A_indices, parallel_A_count, B_sol_indices, trans_B, 1, true);
	getIntersectingLineIndices(intersecting_B_indices, intersection_B_count, parallel_B_indices, parallel_B_count, A_sol_indices, trans_A, 1, false);

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
		
		cout << "Loaded " << all_solution_lines.size() << " solutions to process.\n";
		
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
	cout << "Partial solutions processed: " << partial_count << endl;
	cout << "Time elapsed: " << elapsed << " seconds\n";
	cout << "Throughput: " << (partial_count / elapsed) << " solutions/sec\n";
	cout << "File: " << solution_file << endl;

#if TRACK_TIME == 1
	double sat_total = total_sat_encoding_time + total_sat_solving_time;
	double line_total = total_line_read_time + total_line_finding_time + total_line_parallel_time + total_line_intersection_time;

	cout << "\n=== TOTAL TIMES FOR THIS RUN ===\n";
	cout << "SAT Setup: " << total_sat_setup_time << "s" << endl;
	cout << "SAT Covering: " << total_sat_covering_time << "s" << endl;
	cout << "SAT Intersections: " << total_sat_intersection_time << "s" << endl;
	cout << "SAT Encoding: " << total_sat_encoding_time << "s" << endl; // total of covering, intersection and set up
	cout << "SAT Solving: " << total_sat_solving_time << "s" << endl;
	cout << "SAT Total: " << sat_total << "s" << endl;

	cout << "\nLine Read: " << total_line_read_time << "s" << endl;
	cout << "Line Finding: " << total_line_finding_time << "s" << endl;
	cout << "Line Parallel: " << total_line_parallel_time << "s" << endl;
	cout << "Line Intersection: " << total_line_intersection_time << "s" << endl;
	cout << "Line Total: " << line_total << "s" << endl;

	cout << "\nMissing Time: " << elapsed - (sat_total + line_total) << "s" << endl;
#endif

#if MAX_RUNTIME > 0
	cout << "\nMax Runtime: " << MAX_RUNTIME << " seconds\n";
#endif

	return 0;
}
