import os
import sys
from helpers import *
from encode import *
from decode import *

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)

if len(sys.argv) < 3:
	print("Usage: python3 refinement_from_partial_list.py <template_id> <file_name>\n")
	sys.exit(1)

template_id = int(sys.argv[1]) + 1
solution_file = sys.argv[2]
file_path = os.path.join(script_dir, solution_file)

if not os.path.exists(file_path):
	print("File with these requirements does not exist, ensure that the file is in the same directory as this script and is named <template_id>-<symbol transversal (1-10)>-<partial on A (True/False)>-<partial on B (True/False)>-output.txt")
	sys.exit(1)

order = 10

template_path = os.path.join(parent_dir, "refinements and candidate lines", "templates", str(template_id)+"-template.txt")
candidate_lines_2_path = os.path.join(parent_dir, "refinements and candidate lines", "2-candidate_lines", f"{template_id}-candidate_lines.txt")
candidate_lines_3_path = os.path.join(parent_dir, "refinements and candidate lines", "3-candidate_lines", f"{template_id}-candidate_lines.txt")

exhaust_satsolver_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical-exhaust")
satsolver_path = os.path.join(parent_dir, "kissat-rel-4.0.2", "build", "kissat")

# maybe preprune the output file? could remove the need for checking if something is a solution

points = [set(), set()]
candidate_lines = [[], []]
candidate_line_count = [0, 0]

timeout = -1

print(f"Loading candidate lines for template-{template_id}.")
candidate_lines[0], points[0], candidate_line_count[0] = load_candidate_lines_file(candidate_lines_2_path)
candidate_lines[1], points[1], candidate_line_count[1] = load_candidate_lines_file(candidate_lines_3_path)
total_points = points[0] | points[1]

def isValid(solution, solution_A_lines, solution_B_lines):
	solution_ints = [int(x) for x in solution]
	#print(len(solution_ints), "lines in solution")
	   
	square_A = [[0 for _ in range(order)] for _ in range(order)]
	square_B = [[0 for _ in range(order)] for _ in range(order)]

	lines_A = []
	lines_B = []

	for var in solution_ints:
		if var > 0:
			var -= 1
			if var < len(solution_A_lines):
				line = solution_A_lines[var]
				lines_A.append(line)
				for p in line:
					p -= 1
					r, c = p // order, p % order
					square_A[r][c] += 1
			else:
				var -= len(solution_A_lines)
				if var < len(solution_B_lines):
					line = solution_B_lines[var]
					lines_B.append(line)
					for p in line:
						p -= 1
						r, c = p // order, p % order
						square_B[r][c] += 1
	
	if len(lines_A) != 10 or len(lines_B) != 10:
		print("Invalid solution, does not have 10 lines in each parallel class:", lines_A, lines_B)
		return False
	
	for r in range(order):
		for c in range(order):
			if square_A[r][c] != 1 or square_B[r][c] != 1:
				print("Invalid solution, point", r*order+c+1, "is not covered exactly once by lines in A and B:", square_A[r][c], square_B[r][c])
				return False

	for lineA in lines_A:
		for lineB in lines_B:
			if len(set(lineA) & set(lineB)) != 1: # lines intersect at exactly one point
				print("Lines do not intersect at exactly one point:", lineA, lineB)
				return False

	return True

def getRefinements(solution_id, transversals, solution_A_lines, solution_B_lines, order=10):
	if len(solution_A_lines) < 10:
		#print(f"Solution {solution_id} has {len(solution_A_lines)} lines in A, skipping refinement search.")
		return -1, [] # skip solutions with too few lines in A, as they are unlikely to yield valid refinements and would be expensive to process
	if len(solution_B_lines) < 10:
		#print(f"Solution {solution_id} has {len(solution_B_lines)} lines in B, skipping refinement search.")
		return -2, [] # skip solutions with too few lines in B, as they are unlikely to yield valid refinements and would be expensive to process
	
	# Build SAT instance for finding all valid B completions
	encoding_secondary = SATEncoder(f"B refinement search for solution-{solution_id}", warning_bool=False, use_pipe=True)
	
	a_vars = {}
	b_vars = {}
	for i, line in enumerate(solution_A_lines):
		a_vars[i] = encoding_secondary.new_variable()
	for i, line in enumerate(solution_B_lines):
		b_vars[i] = encoding_secondary.new_variable()
	
	#print(len(solution_A_lines), "A lines and", len(solution_B_lines), "B lines for solution", solution_id)
		
	point_to_A = defaultdict(list)
	point_to_B = defaultdict(list)
	for i, line in enumerate(solution_A_lines):
		for p in line:
			point_to_A[p].append(i)
	for j, line in enumerate(solution_B_lines):
		for p in line:
			point_to_B[p].append(j)
	
	# Fix solution lines (force them to true with unit clauses)
	for i in range(transversals[0]):
		encoding_secondary.add_clause([a_vars[i]])
	for i in range(transversals[1]):
		encoding_secondary.add_clause([b_vars[i]])
	
	# For each point, enforce coverage constraints
	for p in total_points:
		a_indices = point_to_A.get(p, [])
		b_indices = point_to_B.get(p, [])
		if a_indices:
			a_lines = [a_vars[i] for i in a_indices]
			if len(a_lines) < 1:
				#print(len(a_lines), "A lines cover point", p)
				return -3, []
			encoding_secondary.add_forced_cardinality_clause(a_lines, 1, 1)
		if b_indices: 
			b_lines = [b_vars[i] for i in b_indices]
			if len(b_lines) < 1:
				#print(len(b_lines), "B lines cover point", p)
				return -4, []
			encoding_secondary.add_forced_cardinality_clause(b_lines, 1, 1)
	
	def getIntersections(i, j, p1, p2): 
		line_i = None
		line_j = None
		if p1 == 0:
			line_i = solution_A_lines[i]
		else:
			line_i = solution_B_lines[i]
		if p2 == 0:
			line_j = solution_A_lines[j]
		else:
			line_j = solution_B_lines[j]
		return len(set(line_i) & set(line_j))
	
	for i in range(len(solution_A_lines)): 
		for j in range(len(solution_B_lines)): 
			intersections_01 = getIntersections(i, j, 0, 1)
			if intersections_01 != 1: # ensure each line selected is incident once to another in the other parallel class
				encoding_secondary.add_implication_clause([a_vars[i]], [-b_vars[j]])

	encoding_secondary.finalize_encoding()

	solutions = []
	def collect_solution(solution):
		solutions.append(sorted(solution.split()))
		if not isValid(solution.split()[:20], solution_A_lines, solution_B_lines):
			print("Invalid refinement found for solution")

	def parse_secondary_solution(decoder: SATDecoder) -> str:
		return f"B refinement search for solution-{solution_id}"
	
	decoding_secondary = SATDecoder(use_pipe=True, parse_function=parse_secondary_solution)
	
	timeout_command = []
	if timeout > 0:
		timeout_command.append('-t')
		timeout_command.append(str(timeout))

	wall_time = decoding_secondary.run_sat_solver(
		exhaust_satsolver_path,
		input_content=encoding_secondary.to_dimacs(),
		arguments=["--only-neg"] + timeout_command,
		display_to_console=False,
		on_solution_found=collect_solution
	)

	return len(solutions), solutions

# Lists to store solution lines from A and B for all solutions
all_solutions = []
processed_solutions = []
partial_solutions = 0
total_solutions = 0
refinement_time = time.time()

print("Processing each partial solution to find refinements...")
with open(file_path, "r") as f:
	for solution_idx, line in enumerate(f):
		partial_solutions += 1
		solution = [int(x) for x in line.split()[:-1]]
		if solution in processed_solutions:
			continue
		processed_solutions.append(solution)
		transversals = [0,0] # number of transversals in A and B in the partial solution, used to determine which candidate lines are parallel to the solution lines

		# Convert solution from variable indices to grid points split by square
		A_candidate_lines, B_candidate_lines = solutionToCandidateLines(solution, order=10)
		transversals = [len(A_candidate_lines), len(B_candidate_lines)]
		#print(f"Number of candidate lines in A: {len(A_candidate_lines)}, in B: {len(B_candidate_lines)}")

		# Get parallel lines (which also identifies solution lines internally)
		parallel_A, parallel_B = getParallelLines(A_candidate_lines, B_candidate_lines, candidate_lines, candidate_line_count)
		
		# make sure these lines intersect exactly once between the 2 sets, otherwise they can't be part of a valid solution and we can skip the refinement search for this solution
		intersecting_A, intersecting_B = getIntersectingLines(parallel_A, parallel_B, A_candidate_lines, B_candidate_lines, order=10)
		#print("number of parallel lines in A:", len(parallel_A), "number of parallel lines in B:", len(parallel_B))
		#print(f"Solution {solution_idx}: {len(intersecting_A)} intersecting lines in A, {len(intersecting_B)} intersecting lines in B.")
		
		count, solutions = getRefinements(solution_idx, transversals, intersecting_A, intersecting_B, order=10)

		if count > 0:
			total_solutions += count
			all_solutions.append((solution_idx, solutions))
		elif count < 0:
			print(len(intersecting_A), "lines in A and", len(intersecting_B), "lines in B for solution", solution_idx, "skipping refinement search.")
		
		if solution_idx % 100 == 0:
			print(f"Processed {solution_idx} partial solutions, {total_solutions} refinements found so far.")
print(len(all_solutions), "solutions with refinements found out of", len(partial_solutions), "partial solutions processed.")
print("Refinement search took", time.time() - refinement_time, "seconds.")

# 2. test with k=1,2,3,4,5 and include the time to get the solutions then see which is fastest (k to partial solution's transversal count)

# I have checked and the code for parallel lines, intersecting lines and solution to candidate lines (transversals) is correctly implemented in the C++ version.