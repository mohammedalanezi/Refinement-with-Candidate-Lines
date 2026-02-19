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

timeout = 60 * 30

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)

exhaust = True # set to True for exhaustive + parallel processing

exhaust_satsolver_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical-exhaust")
satsolver_path = os.path.join(parent_dir, "kissat-rel-4.0.2", "build", "kissat")

if len(sys.argv) < 5:
	print("Usage: python3 generate.py <template_id> <symbol transversal (1-10)> <partial on A (1/0)> <partial on B (1/0)>\n")
	sys.exit(1)

template_id = int(sys.argv[1]) + 1
order = 10
k_net = []
mapping = {}
variable_counts = {}
latin_squares = 3

observed = []
observed_syms = int(sys.argv[2]) # do partial solution on these symbol transversals
observe_A = int(sys.argv[3]) == 1 #Q
observe_B = int(sys.argv[4]) == 1 #Z

template_path = os.path.join(parent_dir, "refinements and candidate lines", "templates", str(template_id)+"-template.txt")
input_path = os.path.join(script_dir, f"{template_id}-{observed_syms}-{observe_A}-{observe_B}-input.cnf")
output_path = os.path.join(script_dir, f"{template_id}-{observed_syms}-{observe_A}-{observe_B}-output.txt")

if observe_A == False and observe_B == False:
	print("No partial MOLS observed, ensure that the partial solution contains at least one square.")
	sys.exit(1)
if observed_syms <= 0:
	print("No symbols transversals being observed, ensure that we are observing at least one symbol.")
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

if __name__ == "__main__":
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
	encoding.set_encoding_path(input_path, 10000, False)

	Q, Z, P = k_net[0], k_net[1], k_net[2]

	template = unloadTemplate(template_path)
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
			if row == 0:
				relationalCounter = 0
				nonrelationalCounter = 4
				for col, relational in enumerate(line):
					if relational == 1:
						encoding.add_clause([symbols[row][col][relationalCounter]])
						relationalCounter += 1
					else:
						encoding.add_clause([symbols[row][col][nonrelationalCounter]])
						nonrelationalCounter += 1
			if (par_class == 0 and observe_A) or (par_class == 1 and observe_B):
				for col in range(order):
					for sym in range(observed_syms):
						observed.append(symbols[row][col][sym])
							
	
	print("Writing orthogonality constraints.")
	encodeZhangOrthogonality(encoding, P, Q, Z)

	print("Writing latin square constraints.") #  move the bulk of this to encode.py since it will be reused a lot
	for index in range(latin_squares - 1): # maintain latin square clauses
		square = [Q, Z, P][index]
		encodeLatinSquare(encoding, square)
	
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

	encoding.finalize_encoding()
	print(encoding)

	observed_string = " ".join(map(str, observed))

	decoding = decode.SATDecoder(output_path, parseSolution)
	print(f"Running SAT Solver on {input_path}.")
	wall_time = decoding.run_sat_solver(
		exhaust_satsolver_path, 
		input_path,
		["--inprocessing=false", "--observe"] + observed_string.split(),
		False,
	)

	if decoding.get_satisfiability():
		print("Found solutions!")
		count, _ = decoding.get_exhaustive_solutions()
		print(f"Found {count} solutions in the sat instance.")
		timings = decoding.get_timings()
		for key, value in timings.items():
			print(f"Key: {key}, Value: {value}")
	else:
		print("no solution")

