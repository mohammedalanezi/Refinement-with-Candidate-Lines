import os
import sys
import time
from collections import defaultdict
import numpy as np

import encode
import decode

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)

exhaust = True # set to True for exhaustive propagator 

exhaust_satsolver_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical-exhaust")
satsolver_path = os.path.join(parent_dir, "kissat-rel-4.0.2", "build", "kissat")

if len(sys.argv) < 3:
	print("Usage: python3 all_candidate_encoding.py <solution_path> <template_id>\n")
	sys.exit(1)

observed = []
solution_path = sys.argv[1]
template_id = int(sys.argv[2]) + 1
input_path = os.path.join(script_dir, f"{template_id}-input-ac.cnf")
output_path = os.path.join(script_dir, f"{template_id}-output-ac.txt")
candidate_lines_2_path = os.path.join(parent_dir, "refinements and candidate lines", "2-candidate_lines", f"{template_id}-candidate_lines.txt")
candidate_lines_3_path = os.path.join(parent_dir, "refinements and candidate lines", "3-candidate_lines", f"{template_id}-candidate_lines.txt")

points = [set(), set()]
candidate_lines = [[[], []], [[], []]]
candidate_line_count = [0, 0]
order = 10

AB_intersection = []
A_sets = []
B_sets = []

def parseSolution(self: decode.SATDecoder) -> str:
	if self.get_satisfiability() == False or self.get_exhaustive_solutions()[0] > 0:
		return f"No solution found, and so no refinement exists for template-{template_id}."
	else:
		return_string = ""
		timings = self.get_timings()
		count, solutions = self.get_exhaustive_solutions()
		return_string += str(solutions) + "\n"
		return_string += str(timings) + "\n"
		return_string += str(count) + "\n"
		return return_string
	
def load_candidate_lines_file(file_path, p):
	global candidate_line_count
	with open(file_path, "r") as f:
		for line in f:
			candidate_line = line[2:].split()
			if line.startswith("R"):
				candidate_lines[p][0].append(candidate_line)
			elif line.startswith("N"):
				candidate_lines[p][1].append(candidate_line)
			else:
				continue
			candidate_line_count[p] += 1
			for point in candidate_line:
				points[p].add(point)

def getLine(id, p):
	if id < len(candidate_lines[p][0]):
		return candidate_lines[p][0][id]
	else:
		id -= len(candidate_lines[p][0])
		return candidate_lines[p][1][id]

if __name__ == "__main__":
	rewrite = True
	can_forget = True
	
	print("Loading candidate lines from:", candidate_lines_2_path)
	load_candidate_lines_file(candidate_lines_2_path, 0)
	print("Loading candidate lines from:", candidate_lines_3_path)
	load_candidate_lines_file(candidate_lines_3_path, 1)
	for i in range(candidate_line_count[0]):
		A_sets.append(set(getLine(i, 0)))
	for i in range(candidate_line_count[1]):
		B_sets.append(set(getLine(i, 1)))
	total_points = points[0] | points[1]
	
	point_to_A = defaultdict(list)
	point_to_B = defaultdict(list)
	for i in range(candidate_line_count[0]):
		line = getLine(i, 0)
		for p in line:
			point_to_A[p].append(i)
	for j in range(candidate_line_count[1]):
		line = getLine(j, 1)
		for p in line:
			point_to_B[p].append(j)
		
	intersection_time = time.time()
	invalid_intersects = 0

	print("Preloading all A and B candidate line intersections") # use numpy array for efficient storage and sharing
	AB_intersection_np = np.zeros((candidate_line_count[0], candidate_line_count[1]), dtype=np.int8)
	
	for i in range(candidate_line_count[0]):
		for j in range(candidate_line_count[1]):
			AB_intersection_np[i, j] = len(A_sets[i] & B_sets[j])
		if i % 1000 == 0:
			print(f"{i}/{candidate_line_count[0]} ({1000*candidate_line_count[1]} intersections in {(time.time() - intersection_time):.3f}s)")
			intersection_time = time.time()

	if rewrite:
		encoding = encode.SATEncoder("Template Refinement", False)
		open(input_path, "w").close()
		encoding.set_encoding_path(input_path, 10000, False)

		print("Assigning variables to each candidate line.")
		a = [encoding.new_variable() for _ in range(candidate_line_count[0])]
		b = [encoding.new_variable() for _ in range(candidate_line_count[1])]

		print("Enforcing coverage of each point in A by exactly one line.")
		for p in total_points:
			a_indices = point_to_A.get(p, [])
			b_indices = point_to_B.get(p, [])
			if a_indices:
				encoding.add_forced_cardinality_clause([a[i] for i in a_indices], 1, 1)
			if b_indices:
				encoding.add_forced_cardinality_clause([b[i] for i in b_indices], 1, 1)

		print("Enforcing exactly one intersection for each line in one parallel class to the other.")
		for i in range(candidate_line_count[0]): 
			for j in range(candidate_line_count[1]): 
				if AB_intersection_np[i, j] != 1: 
					encoding.add_implication_clause([a[i]], [-b[j]])
					invalid_intersects += 1
			if i % 1000 == 0:
				print(f"{i}/{candidate_line_count[0]} ({invalid_intersects} in {(time.time() - intersection_time):.3f}s)")
				intersection_time = time.time()
				invalid_intersects = 0

		encoding.finalize_encoding()
		print(encoding)

	for s in range(candidate_line_count[0]):
		observed.append(s + 1)

	observed_string = " ".join(map(str, observed))
	forget = []

	if can_forget:
		forget.append("--can-forget")

	decoding = decode.SATDecoder(output_path, parseSolution)
	print(f"Running SAT Solver on {input_path}.")
	wall_time = decoding.run_sat_solver(
		exhaust_satsolver_path, 
		input_path,
		forget + ["--solfile", solution_path, "--observe"] + observed_string.split(), #+ ["--inprocessing=false"], # + ["-t", "4"]
		True,
	)
	print("Found solutions, output written to", solution_path)
	print(f"Found {decoding.solution_count} solutions in the sat instance.")
	print(f"Timings: {decoding.timings}")
