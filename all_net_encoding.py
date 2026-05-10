'''
All Net Encoding by Mohammed

Parallel processing version for exhaustive SAT solutions
Finds every single possible A in valid AB pairs
'''

import os
import sys

from helpers import *
import encode
import decode

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)

exhaust_satsolver_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical-exhaust")
satsolver_path = os.path.join(parent_dir, "kissat-rel-4.0.2", "build", "kissat")

if len(sys.argv) < 6:
    print("Usage: python3 all_net_encoding.py <solution file name> <template_id> <symbol transversals on A (0-10)> <symbol transversals on B (0-10)> <common disjoint transversals (0-10)> <common transversals>\n")
    sys.exit(1)

solution_file = sys.argv[1]

template_id = int(sys.argv[2]) + 1
order = 10
k_net = []
mapping = {}
variable_counts = {}
latin_squares = 3

observed = []
observed_syms_A = int(sys.argv[3]) # do partial solution on these symbol transversals for A
observed_syms_B = int(sys.argv[4]) # do partial solution on these symbol transversals for A
num_common_transversals = int(sys.argv[5])

template_path = os.path.join(parent_dir, "refinements and candidate lines", "templates", str(template_id)+"-template.txt")

if observed_syms_A > 10 or observed_syms_B > 10:
	print("Too many symbols in the latin squares are observed, ensure that at most 10 symbols are observed in either latin square.")
	sys.exit(1)
if observed_syms_A <= 0 and observed_syms_B <= 0:
	print("No symbols transversals being observed, ensure that we are observing at least one symbol from either latin square.")
	sys.exit(1)

# FOR JUST PARTIAL SOLUTIONS OVER As SET observe_A = True, observe_B = False, and observed_syms = order

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

def get4DIndex(index): 
	tuple = mapping[index]
	return tuple[0], tuple[1] - 1, tuple[2] - 1, tuple[3] - 1

def runEncoding(can_forget=False, suffix=""):
	filename = f"{template_id}-{observed_syms_A}-{observed_syms_B}-{num_common_transversals}"
	if suffix != "":
		filename += f"-{suffix}"
	input_path = os.path.join(script_dir, f"{filename}-input.cnf")
	output_path = os.path.join(script_dir, f"{filename}-output.txt")
	solution_path = os.path.join(script_dir, solution_file)
	template = unloadTemplate(template_path)
	encoding = encode.SATEncoder("As Encoding for Template Refinement", False)
	
	def addSquareVariables(table : list, square : int):
		variable_counts[square] = 0
		for _ in range(order):
			table.append([])
			for _ in range(order):
				table[-1].append([])
				for _ in range(order):
					var = encoding.new_variable()
					table[-1][-1].append(var)
					mapping[var] = (square, len(table), len(table[-1]), len(table[-1][-1]))
					variable_counts[square] += 1

	for i in range(latin_squares):
		k_net.append([])
		addSquareVariables(k_net[-1], i)
		
	open(input_path, "w").close()
	open(solution_path, "w").close()
	encoding.set_encoding_path(input_path, 10000, False)

	Q, Z, P = k_net[0], k_net[1], k_net[2]

	print("Writing latin square constraints.")
	for index in range(latin_squares): # maintain latin square clauses
		square = [Q, Z, P][index]
		encodeLatinSquareOld(encoding, square)

	print("Writing orthogonality constraints.")
	encodeMyrvoldOrthogonality(encoding, P, Q, Z)
	
	print("Writing symmetry breaking.")
	for par_class, lines in enumerate(template):
		symbols = [Q, Z][par_class]
		relationalCounter = 0
		nonrelationalCounter = 4
		for col, relational in enumerate(lines[0]):
			if relational == 1:
				encoding.add_clause([symbols[0][col][relationalCounter]])
				relationalCounter += 1
			else:
				encoding.add_clause([symbols[0][col][nonrelationalCounter]])
				nonrelationalCounter += 1
	
	for i in range(order): # from gill encoding
		ri = (i in range(4))
		for j in range(order):
			rj = (j in range(4))
			for s in range(order):
				rs = (s in range(4))
				for t in range(order):
					rt = (t in range(4))
					if (ri + rj + rs + rt) % 2 == 1:
						encoding.add_clause([-Q[i][j][s], -Z[i][j][t]])

	print("Writing template restrictions.")
	for par_class, lines in enumerate(template):
		symbols = [Q, Z][par_class]
		for row, line in enumerate(lines):
			for col, relational in enumerate(line):
				if relational == 1:
					for s in range(4,order):
						encoding.add_clause([-symbols[row][col][s]])
				else:
					for s in range(4):
						encoding.add_clause([-symbols[row][col][s]])

	if num_common_transversals > 0: # Seems to only be viable in cases where we 100% know that we have transversals in A and B
		# transversal_sym_in_Z[k][j][s] = True -> the cell that Q assigns symbol k in column j has symbol s in Z
		transversal_sym_in_Z = [[[encoding.new_variable() for s in range(order)] for j in range(order)] for k in range(order)]
		# We only need this auxiliary for Z (Q's own variables already define the transversal)

		# Force unused slots to false
		for k in range(num_common_transversals, order):
			for j in range(order):
				for s in range(order):
					encoding.add_clause([-transversal_sym_in_Z[k][j][s]])

		# For each active transversal k, enforce that transversal_sym_in_Z[k] is a bijection, i.e. the cells of Q's symbol-k slice carry all 10 symbols in Z
		for k in range(num_common_transversals):
			for i in range(order):
				# Each symbol s appears exactly once across columns (symbol i used as both)
				encoding.add_clause([transversal_sym_in_Z[k][j][i] for j in range(order)])
				for j in range(order):
					for j2 in range(j + 1, order):
						encoding.add_clause([-transversal_sym_in_Z[k][j][i], -transversal_sym_in_Z[k][j2][i]])
				# Each column has exactly one symbol
				encoding.add_clause([transversal_sym_in_Z[k][i][s] for s in range(order)])
				for s in range(order):
					for s2 in range(s + 1, order):
						encoding.add_clause([-transversal_sym_in_Z[k][i][s], -transversal_sym_in_Z[k][i][s2]])

		# if Q[i][j]=k (cell (i,j) is on transversal k) and Z[i][j]=s, then transversal k carries symbol s in column j in Z, and vice versa
		for i in range(order):
			for j in range(order):
				for k in range(num_common_transversals):
					for s in range(order):
						encoding.add_clause([-Q[i][j][k], -Z[i][j][s],  transversal_sym_in_Z[k][j][s]])
						encoding.add_clause([-Q[i][j][k], -transversal_sym_in_Z[k][j][s],  Z[i][j][s]])
						encoding.add_clause([-Z[i][j][s], -transversal_sym_in_Z[k][j][s],  Q[i][j][k]])

	encoding.finalize_encoding()
	print(encoding)

	for s in range(observed_syms_A):
		for r in range(order):
			for c in range(order):
				observed.append(Q[r][c][s])

	for s in range(observed_syms_B):
		for r in range(order):
			for c in range(order):
				observed.append(Z[r][c][s])

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

		# TODO: move --solfile to decode.py and maybe edit cadical-exhaust to output solfile location to console at the start

	print("Found solutions, output written to", solution_path)
	print(f"Found {decoding.solution_count} solutions in the sat instance.")
	print(f"Timings: {decoding.timings}")
		
if __name__ == "__main__":
	runEncoding(True, "can_forget with inprocessing off")
	# TODO: maybe make a clean up helper function and run it in runEncoding when forget is True

# forget flag present is faster than forget flag not present, but results in more solutions (as expected)
# 	fastest combination is with inprocessing on and can-forget on
#   I think inprocessing off is only faster than inprocessing on when can-forget is false

	
# TODO: need to update external propagator to write to solution file only the non duplicate solutions, e.g. using my hashing algorithm