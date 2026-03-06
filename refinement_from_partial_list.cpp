#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <set>
#include <unordered_set>
#include <string>
#include <tuple>
#include <chrono>
#include <algorithm>
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <unistd.h>
#include <fcntl.h>

#include <omp.h>
#include <mutex>

#include "cadical.hpp"
#include "exhaustive.hpp"

using namespace std;

#define PRINT_TIME 0
#define TRACK_TIME 1

// Global data structures
const int order = 10;

vector<vector<int>> cand_lines_A;
vector<vector<int>> cand_lines_B;
unordered_set<int> points_A;
unordered_set<int> points_B;
unordered_set<int> total_points;

vector<vector<int>> intersections_AB; // intersections_AB[i][j] = number of intersections between cand_lines_A[i] and cand_lines_B[j]
vector<vector<int>> parallels_A;
vector<vector<int>> parallels_B;

vector<int> all_line_indices_A;
vector<int> all_line_indices_B;

long partial_count = 0;
int count_A = 0;
int count_B = 0;

#if TRACK_TIME == 1 
double total_sat_solving_time = 0.0; // wall time
double total_sat_encoding_time = 0.0;
double total_sat_covering_time = 0.0;
double total_sat_intersection_time = 0.0;
double total_sat_setup_time = 0.0;
double total_sat_time = 0.0;

double total_line_finding_time = 0.0;
double total_line_parallel_time = 0.0;
double total_line_intersection_time = 0.0;
double total_line_time = 0.0;
#endif

struct Mask {
    uint64_t lo = 0; // bits 0–63
    uint64_t hi = 0; // bits 64–127
};

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

int computeIntersectionCountMask(const Mask& m1, const Mask& m2) { // compute intersection count between two masks
    return __builtin_popcountll(m1.lo & m2.lo) + __builtin_popcountll(m1.hi & m2.hi);
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

tuple<vector<vector<int>>, unordered_set<int>, int> load_candidate_lines_file(const string& path) {
	ifstream f(path);
	vector<vector<int>> lines;
	unordered_set<int> points;
	string line;
	while (getline(f, line)) {
		if (line.empty()) continue;
		char prefix = line[0];
		if (prefix == 'R' || prefix == 'N') {
			vector<int> nums = parse_line(line, prefix);
			if (!nums.empty()) {
				lines.push_back(nums);
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

pair<vector<vector<int>>, vector<vector<int>>> solutionToCandidateLines(const vector<int>& solution) {
	vector<vector<int>> points_by_symbol[2];
	for (int sq = 0; sq < 2; ++sq)
		points_by_symbol[sq].resize(order);

	for (int var : solution) {
		if (var <= 0) continue;
		auto [sq, r, c, s] = indexTo4Tuple(var, 2, order, order, order);
		int point = get1DIndex(r, c);
		points_by_symbol[sq][s].push_back(point);
	}

	vector<vector<int>> A_lines, B_lines;
	for (int sq = 0; sq < 2; ++sq)
		for (int s = 0; s < order; ++s)
			if ((int)points_by_symbol[sq][s].size() == order) {
				if (sq == 0) 
					A_lines.push_back(points_by_symbol[sq][s]);
				else 
					B_lines.push_back(points_by_symbol[sq][s]);
			}
	return {A_lines, B_lines};
}

vector<int> findLineIndices(const vector<vector<int>>& solution_lines, const vector<vector<int>>& candidate_lines) {
    vector<int> indices; // converts solution lines to their candidate line indices
    indices.reserve(solution_lines.size());
    
    for (const auto& sol_line : solution_lines) // find matching candidate line
        for (size_t i = 0; i < candidate_lines.size(); ++i)
            if (candidate_lines[i] == sol_line) {
                indices.push_back(i);
                break;
            }
    
    return indices;
}

void precomputeDataStructures() {
    auto start = chrono::steady_clock::now();
    
    intersections_AB.resize(cand_lines_A.size());
    for (size_t i = 0; i < cand_lines_A.size(); ++i) {
        intersections_AB[i].resize(cand_lines_B.size());
        for (size_t j = 0; j < cand_lines_B.size(); ++j) {
            intersections_AB[i][j] = computeIntersectionCountMask(cand_masks_A[i], cand_masks_B[j]);
        }
    }
	
    parallels_A.reserve(cand_lines_A.size());
    for (size_t i = 0; i < cand_lines_A.size(); ++i) {
        parallels_A[i].reserve(cand_lines_A.size());
        for (size_t j = 0; j < cand_lines_A.size(); ++j) {
			int inter = computeIntersectionCountMask(cand_masks_A[i], cand_masks_A[j]);
			if(inter == 0)
				parallels_A[i].push_back(j);
        }
    }
	
    parallels_B.reserve(cand_lines_B.size());
    for (size_t i = 0; i < cand_lines_B.size(); ++i) {
        parallels_B[i].reserve(cand_lines_B.size());
        for (size_t j = 0; j < cand_lines_B.size(); ++j) {
			int inter = computeIntersectionCountMask(cand_masks_B[i], cand_masks_B[j]);
			if(inter == 0)
            	parallels_B[i].push_back(j);
        }
    }

	all_line_indices_A.reserve(cand_lines_A.size());
	for(int i = 0; i < cand_lines_A.size(); i++)
		all_line_indices_A.push_back(i);
		
	all_line_indices_B.reserve(cand_lines_B.size());
	for(int i = 0; i < cand_lines_B.size(); i++)
		all_line_indices_B.push_back(i);
    
    auto end = chrono::steady_clock::now();
    double elapsed = chrono::duration<double>(end - start).count();
    cout << "Precomputed intersections using masks in " << elapsed << " seconds." << endl;
    //cout << "  A-B: " << cand_lines_A.size() << "x" << cand_lines_B.size() << " = " << (cand_lines_A.size() * cand_lines_B.size()) << " entries" << endl;
}

vector<int> getAllParallelLineIndices(const vector<int>& line_indices, const int& length, bool is_A) {
    const auto& parallels   = is_A ? parallels_A   		 : parallels_B;
    const auto& candidates  = is_A ? cand_lines_A  		 : cand_lines_B;
    const auto& all			= is_A ? all_line_indices_A  : all_line_indices_B;
    vector<int> result;

    if (line_indices.empty()) {
        return all;
	}

    if (line_indices.size() == 10) {
        return line_indices;
	}
	
    result.reserve(line_indices.size()); // initial known size
    result.insert(result.end(), line_indices.begin(), line_indices.end());

    vector<int> intersection = parallels[line_indices[0]];

    for (size_t i = 1; i < line_indices.size() && !intersection.empty(); ++i) {
        const vector<int>& current = parallels[line_indices[i]];

        vector<int> temp;
		if(intersection.size() < current.size())
			temp.reserve(intersection.size());
		else
			temp.reserve(current.size());

        size_t p1 = 0, p2 = 0;
        const size_t s1 = intersection.size();
        const size_t s2 = current.size();

        while (p1 < s1 && p2 < s2) {
            if (intersection[p1] < current[p2]) {
                ++p1;
            } else if (intersection[p1] > current[p2]) {
                ++p2;
            } else {
                temp.push_back(intersection[p1]);
                ++p1;
                ++p2;
            }
        }

        intersection.swap(temp);
    }

    result.insert(result.end(), intersection.begin(), intersection.end());
    return result;
}

vector<int> getIntersectingLineIndices(const vector<int>& line_indices, const vector<int>& opposite_indices, int intersections, bool is_A) {
    vector<int> intersecting_indices;
    
    for (int line_idx : line_indices) {
        bool valid = true;
        
        for (int opp_idx : opposite_indices) { // VECTOR
            int inter;
            if (is_A) 
                inter = intersections_AB[line_idx][opp_idx];
            else 
                inter = intersections_AB[opp_idx][line_idx];
            
            if (inter != intersections) {
                valid = false;
                break;
            }
        }
        
        if (valid) 
            intersecting_indices.push_back(line_idx);
    }
    
    return intersecting_indices;
}

int get_refinements(const pair<int,int>& transversals, const vector<int>& solution_A_indices, const vector<int>& solution_B_indices) {
#if TRACK_TIME == 1
    auto timer = chrono::steady_clock::now();
#endif
    
    vector<int> observed;
    CaDiCaL::Solver solver;

    const size_t a_count = solution_A_indices.size();
    const size_t b_count = solution_B_indices.size();

	int var_cnt = a_count + b_count;

    if (transversals.first < 0 || transversals.second < 0 || transversals.first > 10 || transversals.second > 10) {
        return -1;
    }

	vector<int> cell_map[order * order * 10];
	for (int i = 0; i < order * order * 2; i++) {
		if(i < order * order)
			cell_map[i].reserve(a_count);
		else
			cell_map[i].reserve(b_count);
	}
    
    for (size_t i = 0; i < a_count; i++) 
        for (int p : cand_lines_A[solution_A_indices[i]]) {
            cell_map[p - 1].push_back(i + 1);
        }
    for (size_t i = 0; i < b_count; i++)
        for (int p : cand_lines_B[solution_B_indices[i]]) {
            cell_map[p - 1 + order * order].push_back(i + 1 + a_count);
        }

#if TRACK_TIME == 1
    double setup_elapsed = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	timer = chrono::steady_clock::now();
#endif

	const int total_cells = order * order * 2;
	for (int idx = 0; idx < total_cells; idx++) {
		const vector<int>& cell = cell_map[idx];
		const int cell_size = cell.size();
		
		if (cell_size == 0)
			return -2;
		
		solver.clause(cell); // at-least-one clause
        
        if(cell_size > 1) // skip single covers
            for (int i = 0; i < cell_size; i++) { // at-most-one clauses
                const int lit_i = cell[i];
                for (int j = i+1; j < cell_size; j++) {
                    solver.clause(-lit_i, -cell[j]);
                }
            }
	}

#if TRACK_TIME == 1
    double covering_elapsed = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	timer = chrono::steady_clock::now();
#endif

    if(transversals.first > 0 && transversals.second > 0) {
        for (size_t i = 0; i < a_count; i++) {
            const int a_idx = solution_A_indices[i];
            const int a_var = i + 1;
        	const auto& intersection_row = intersections_AB[a_idx];
            
            for (size_t j = 0; j < b_count; j++) {
				int b_idx = solution_B_indices[j]; 
				if (intersection_row[b_idx] != 1) {
						solver.clause(-a_var, -(a_count + j + 1));
					}
				}
        }
    }
    
    ExhaustiveSearch propagator(&solver, observed, true, nullptr, false);	
    
#if TRACK_TIME == 1
    double intersections_elapsed = chrono::duration<double>(chrono::steady_clock::now() - timer).count();
	timer = chrono::steady_clock::now();
#endif

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
	total_sat_time += covering_elapsed + intersections_elapsed + setup_elapsed + solver_elapsed;
#endif

    return sol_count;
}

// Modified to work with indices
int processLine(string& line)
{
	if (line.empty()) 
		return 0;
	if (line.back() == '0') {
		line.pop_back();
	}
	istringstream iss(line);
	vector<int> solution(100);
	int x;
	while (iss >> x)
		if (x != 0) 
			solution.push_back(x);

	++partial_count;
	
#if TRACK_TIME == 1
	auto conversion_time = chrono::steady_clock::now();
#endif 

	auto [A_sol_lines, B_sol_lines] = solutionToCandidateLines(solution);
	int trans_A = A_sol_lines.size();
	int trans_B = B_sol_lines.size();
	
#if TRACK_TIME == 1
	double elapsed_1 = chrono::duration<double>(chrono::steady_clock::now() - conversion_time).count();
	auto index_time = chrono::steady_clock::now();
#endif
	
	// Convert solution lines to their candidate line indices
	vector<int> A_sol_indices = findLineIndices(A_sol_lines, cand_lines_A);
	vector<int> B_sol_indices = findLineIndices(B_sol_lines, cand_lines_B);
	
#if TRACK_TIME == 1
	double elapsed_index = chrono::duration<double>(chrono::steady_clock::now() - index_time).count();
	auto parallel_time = chrono::steady_clock::now();
#endif

	vector<int> parallel_A_indices = getAllParallelLineIndices(A_sol_indices, cand_lines_A.size(), true);
	vector<int> parallel_B_indices = getAllParallelLineIndices(B_sol_indices, cand_lines_B.size(), false);

#if TRACK_TIME == 1
	double elapsed_2 = chrono::duration<double>(chrono::steady_clock::now() - parallel_time).count();
	auto intersection_time = chrono::steady_clock::now();
#endif

	// Filter to those that intersect exactly once with every line of the opposite square's solution using precomputed intersections
	vector<int> intersecting_A_indices = getIntersectingLineIndices(parallel_A_indices, B_sol_indices, 1, true);
	vector<int> intersecting_B_indices = getIntersectingLineIndices(parallel_B_indices, A_sol_indices, 1, false);
	
#if TRACK_TIME == 1
	double elapsed_3 = chrono::duration<double>(chrono::steady_clock::now() - intersection_time).count();
	#if PRINT_TIME == 1
	cout << "Conversion Time: " << elapsed_1 << ", Index Finding: " << elapsed_index << ", Parallel Time: " << elapsed_2 << ", Intersection Time: " << elapsed_3 << " (Total: " << (elapsed_1 + elapsed_index + elapsed_2 + elapsed_3) << ")" << endl;
	#endif
	total_line_finding_time += elapsed_1;
	total_line_parallel_time += elapsed_2;
	total_line_intersection_time += elapsed_3;
	total_line_time += elapsed_1 + elapsed_2 + elapsed_3;
#endif

	long int refinement_count = get_refinements({trans_A, trans_B}, intersecting_A_indices, intersecting_B_indices);

	return refinement_count;
}

// ------------------------------------------------------------
// Main
// ------------------------------------------------------------
int main(int argc, char* argv[]) {
	if (argc < 4) {
		cerr << "Usage: " << argv[0] << " <template_id> <file_name> <is_multithreaded>\n";
		return 1;
	}

	int template_id = atoi(argv[1]) + 1;
	string solution_file = argv[2];
	bool useMultiThreading = atoi(argv[3]) == 1;

	string parent_dir = "../refinements and candidate lines/";
	string candidate_lines_2_path = parent_dir + "2-candidate_lines/" + to_string(template_id) + "-candidate_lines.txt";
	string candidate_lines_3_path = parent_dir + "3-candidate_lines/" + to_string(template_id) + "-candidate_lines.txt";

	tie(cand_lines_A, points_A, count_A) = load_candidate_lines_file(candidate_lines_2_path);
	tie(cand_lines_B, points_B, count_B) = load_candidate_lines_file(candidate_lines_3_path);

	total_points = points_A;
	total_points.insert(points_B.begin(), points_B.end());
	
	auto start_time = chrono::steady_clock::now(); // Precompute masks
	cout << "Precomputing masks for candidate lines..." << endl;
	cand_masks_A.reserve(cand_lines_A.size());
	for (const auto& line : cand_lines_A) {
		cand_masks_A.push_back(make_mask(line));
	}
	cand_masks_B.reserve(cand_lines_B.size());
	for (const auto& line : cand_lines_B) {
		cand_masks_B.push_back(make_mask(line));
	}
	cout << "Mask time: " << chrono::duration<double>(chrono::steady_clock::now() - start_time).count() << endl;
	
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
	if(useMultiThreading == false) {
		string line;
		while (getline(sol_stream, line))
			if (!line.empty())
				if (seen.insert(line).second) {
					long int refinement_count = processLine(line); 
					if(refinement_count > 0)
						total_refinements += refinement_count;
					if (partial_count % 100 == 0) {
						auto current_time = chrono::steady_clock::now();
						double elapsed = chrono::duration<double>(current_time - start_time).count();
						cout << "Processed " << partial_count << " partial solutions. Time elapsed: " << elapsed << " seconds with total refinements: " << total_refinements << endl;
					}
				}
		sol_stream.close();
	} else {
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
		
		auto max_threads = omp_get_max_threads();
		int limit_threads = 2;

		omp_set_num_threads(max(1, max_threads - limit_threads));
		
		start_time = chrono::steady_clock::now();
		#pragma omp parallel for schedule(dynamic)
		for (size_t sol_idx = 0; sol_idx < all_solution_lines.size(); sol_idx++) {
			string& line = all_solution_lines[sol_idx];
			long int refinement_count = processLine(line); 
			if (refinement_count > 0) {
				#pragma omp atomic
				total_refinements += refinement_count;

				#pragma omp critical
				{
					cout << "Solution " << sol_idx + 1 << " has " << refinement_count << " refinements. Total so far: " << total_refinements << endl;
				}
			}
			if (partial_count % 100 == 0) {
				auto current_time = chrono::steady_clock::now();
				double elapsed = chrono::duration<double>(current_time - start_time).count();
				
				#pragma omp critical
				{
					cout << "Processed " << partial_count << " partial solutions. Time elapsed: " << elapsed << " seconds with total refinements: " << total_refinements << endl;
				}
			}
		}
	}

	auto end_time = chrono::steady_clock::now();
	double elapsed = chrono::duration<double>(end_time - start_time).count();
	
	cout << "\n=== FINAL RESULTS FOR TEMPLATE " << template_id << " ===\n";
	cout << "Total refinements found: " << total_refinements << endl;
	cout << "Partial solutions processed: " << partial_count << endl;
	cout << "Time elapsed: " << elapsed << " seconds\n";
	cout << "Throughput: " << (partial_count / elapsed) << " solutions/sec\n";
	cout << "File: " << solution_file << endl;

	#if TRACK_TIME == 1
	cout << "\n=== TOTAL TIMES FOR THIS RUN ===\n";
	cout << "SAT Solving: " << total_sat_solving_time << endl;
	cout << "SAT Encoding: " << total_sat_encoding_time << endl;
	cout << "SAT Covering: " << total_sat_covering_time << endl;
	cout << "SAT Intersections: " << total_sat_intersection_time << endl;
	cout << "SAT Setup: " << total_sat_setup_time << endl;
	cout << "SAT Total: " << total_sat_time << endl;

	cout << "\nLine Finding: " << total_line_finding_time << endl;
	cout << "Line Parallel: " << total_line_parallel_time << endl;
	cout << "Line Intersection: " << total_line_intersection_time << endl;
	cout << "Line Total: " << total_line_time << endl;
	#endif

	return 0;
}
