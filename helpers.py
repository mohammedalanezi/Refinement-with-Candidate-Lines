"""
Helper for my functions that don't belong to either encoding SAT or decoding SAT.

By Mohammed Al-Anezi.
"""

import subprocess
import time
from io import StringIO
from collections import defaultdict

def indexTo4Tuple(var_index, num_squares, num_rows, num_cols, num_symbols):
	"""
	Convert a flat variable index to a 4D tuple (square, row, col, symbol).
	
	The encoding layout is:
	- Variables are numbered sequentially 1, 2, 3, ...
	- Each square has num_rows * num_cols * num_symbols variables
	- Within a square: offset = row * (num_cols * num_symbols) + col * num_symbols + symbol
	
	Args:
		var_index: 1-indexed variable number
		num_squares: Number of Latin squares (typically 3: Q, Z, P)
		num_rows: Number of rows per square (typically 10)
		num_cols: Number of columns per square (typically 10)
		num_symbols: Number of symbols per square (typically 10)
	
	Returns:
		(square, row, col, symbol) tuple, all 0-indexed
	"""
	vars_per_square = num_rows * num_cols * num_symbols
	adjusted_index = var_index - 1  # Convert to 0-indexed
	
	square = adjusted_index // vars_per_square
	offset_in_square = adjusted_index % vars_per_square
	
	symbol = offset_in_square % num_symbols
	remainder = offset_in_square // num_symbols
	col = remainder % num_cols
	row = remainder // num_cols
	
	return (square, row, col, symbol)

def load_candidate_lines_file(file_path):
	candidate_lines = [[], []]
	points = set()
	counter = 0
	with open(file_path, "r") as f:
		for line in f:
			candidate_line = [int(i) for i in line[2:].split()]
			if line.startswith("R"):
				candidate_lines[0].append(candidate_line)
			elif line.startswith("N"):
				candidate_lines[1].append(candidate_line)
			else:
				continue
			counter += 1
			for point in candidate_line:
				points.add(point)
	return candidate_lines, points, counter

def getLine(id, candidate_lines):
	if id < len(candidate_lines[0]):
		return candidate_lines[0][id]
	else:
		id -= len(candidate_lines[0])
		return candidate_lines[1][id]

def pointsToLine(lines, count):
	point_to_lines = defaultdict(list)
	for i in range(count):
		line = getLine(i, lines)
		for p in line:
			point_to_lines[p].append(i)
	return point_to_lines

def unloadTemplate(path):
	template = [[], []]
	with open(path, "r") as f:
		for i, line in enumerate(f):
			line = line.strip()
			if len(line) > 0:
				if i <= 9:
					template[0].append([])
					for s in list(line):
						template[0][-1].append(int(s))
				if i > 10 and i <= 20:
					template[1].append([])
					for s in list(line):
						template[1][-1].append(int(s))
	return template

def get1DIndex(r, c, order=10):
	return r * order + c + 1

def checkValid(square):
	n = len(square)
	if any(len(row) != n for row in square): # All rows are length n
		return False
	for row in square: # Each row contains all symbols 0 to n-1 exactly once
		if sorted(row) != list(range(n)):
			return False
	for col_idx in range(n): # Each column contains all symbols 0 to n-1 exactly once
		col = [square[row_idx][col_idx] for row_idx in range(n)]
		if sorted(col) != list(range(n)):
			return False
	return True

def checkOrthogonal(square1, square2):
	order = len(square1)
	exists = []
	for i in range(order):
		for j in range(order):
			pair = (square1[i][j], square2[i][j])
			if pair in exists:
				return False
			exists.append(pair)
	return True

def encodeLatinSquare(encoding, square):
	order = len(square)
	for x in range(order):
		for y in range(order): # create at least one value clause for row, col and symbol
			clause3 = [] # sym
			for z in range(order):
				clause3.append(square[x][y][z]) 
				for w in range(z + 1, order): # at most one symbol (binary exclusions)
					encoding.add_clause([-square[x][y][z], -square[x][y][w]])
					encoding.add_clause([-square[x][z][y], -square[x][w][y]])
					encoding.add_clause([-square[z][x][y], -square[w][x][y]])
			encoding.add_clause(clause3)

def encodeZhangOrthogonality(encoding, P, A, B):
	'''
	Encode orthogonality between A and B using an auxiliary latin square P.
	This code is from Aaron Barnoff and derived from Zhang H. in https://dl.acm.org/doi/10.5555/271101.271124
	
	:param encoding: SATEncoder object, the current sat instance
	:param P: Axuiliary Latin Square for Traversal and Orthogonality
	:param A: First Latin Square
	:param B: Second Latin Square
	'''
	order = len(P)
	# a/b belongs to column q: if A[p][q]=a and B[p][q]=b then P[q]=(a/b)
	for row in range(order):
		for col in range(order):
			for sym_1 in range(order):
				for sym_2 in range(order):
					encoding.add_clause([-A[row][col][sym_1], -B[row][col][sym_2], P[col][sym_1][sym_2]])
	# a/b belongs to column q: if A[p][q]=a and P[q]=(a/b) then B[p][q]=b 
	for row in range(order):
		for col in range(order):
			for sym_1 in range(order):
				for sym_2 in range(order):
					encoding.add_clause([-A[row][col][sym_1], B[row][col][sym_2], -P[col][sym_1][sym_2]])
	# a/b belongs to column q: if B[p][q]=b and P[q]=(a/b) then A[p][q]=a
	for row in range(order):
		for col in range(order):
			for sym_1 in range(order):
				for sym_2 in range(order):
					encoding.add_clause([A[row][col][sym_1], -B[row][col][sym_2], -P[col][sym_1][sym_2]])   
	# a/b can only be in one column: if P[q]=a/b then P[t]!=a/b, for all q!=t.
	for col_1 in range(order):
		for col_2 in range(col_1+1, order):
			for sym_1 in range(order):
				for sym_2 in range(order):
					encoding.add_clause([-P[col_1][sym_1][sym_2],-P[col_2][sym_1][sym_2]])    

def encodeMyrvoldOrthogonality(encoding, P, Q, Z):
	'''
	Encode orthogonality between Q and Z using an auxiliary latin square P.
	
	:param encoding: SATEncoder object, the current sat instance
	:param P: Axuiliary Latin Square for Traversal and Orthogonality
	:param Q: First Latin Square
	:param Z: Second Latin Square
	'''
	order = len(P)
	for i in range(order): # orthogonality using auxiliary matrix P
		for i_prime in range(order):
			for j in range(order):
				for k in range(order):
					p, q, z = P[i_prime][j][k], Q[i][j][k], Z[i][j][i_prime]
					encoding.add_implication_clause([z, p], [q])
					encoding.add_implication_clause([z, q], [p])
					encoding.add_implication_clause([p, q], [z])

def encodeLatinSquareOld(encoding, square):
	order = len(square)
	for x in range(order):
		for y in range(order): # create at least one value clause for row, col and symbol
			clause1 = [] # row
			clause2 = [] # col
			clause3 = [] # sym
			for z in range(order):
				clause1.append(square[x][y][z])
				clause2.append(square[x][z][y]) 
				clause3.append(square[z][x][y]) 
				for w in range(z + 1, order): # at most one symbol (binary exclusions)
					encoding.add_clause([-square[x][y][z], -square[x][y][w]])
					encoding.add_clause([-square[x][z][y], -square[x][w][y]])
					encoding.add_clause([-square[z][x][y], -square[w][x][y]])
			encoding.add_clause(clause1)
			encoding.add_clause(clause2)
			encoding.add_clause(clause3)

def getParallelLines(A_candidate_lines, B_candidate_lines, candidate_lines, counts, order=10):
	parallel_A = []
	parallel_B = []

	for i in range(len(A_candidate_lines)):
		parallel_A.append(A_candidate_lines[i])
	for i in range(len(B_candidate_lines)):
		parallel_B.append(B_candidate_lines[i])

	# Check A candidate lines for parallelism with solution lines
	for i in range(counts[0]):
		line = getLine(i, candidate_lines[0])
		line_set = set(line)
		
		isParallel = True

		for j in range(len(A_candidate_lines)):
			solution_line = A_candidate_lines[j]
			solution_line_set = set(solution_line)
			
			if len(line_set & solution_line_set) > 0:
				isParallel = False
				break

		if isParallel:
			parallel_A.append(line)
	
	# Check B candidate lines for parallelism with solution lines
	for i in range(counts[1]):
		line = getLine(i, candidate_lines[1])
		line_set = set(line)
		
		isParallel = True

		for j in range(len(B_candidate_lines)):
			solution_line = B_candidate_lines[j]
			solution_line_set = set(solution_line)
			
			if len(line_set & solution_line_set) > 0:
				isParallel = False
				break

		if isParallel:
			parallel_B.append(line)

	return parallel_A, parallel_B

def solutionToCandidateLines(solution, order=10):
	A_candidate_lines = []
	B_candidate_lines = []

	for l in range(2): # for A and B squares
		for s in range(order):
			transversal = []
			for r in range(order):
				for c in range(order):
					var_index = l * order * order * order + r * order * order + c * order + s + 1
					if var_index in solution:
						point_index = r * order + c + 1
						transversal.append(point_index)
			if len(transversal) >= order:
				if l == 0: 
					A_candidate_lines.append(transversal)
				else:
					B_candidate_lines.append(transversal)
					
	return A_candidate_lines, B_candidate_lines
	
def getIntersectingLines(parallel_A, parallel_B, A_partial_solution_lines, B_partial_solution_lines, order=10):
	intersecting_A = []
	intersecting_B = []

	for line_A in parallel_A:
		allowed = True
		for line_B in B_partial_solution_lines:
			if len(set(line_A) & set(line_B)) != 1: # lines intersect at exactly one point
				allowed = False
				break
		if allowed:
			intersecting_A.append(line_A)

	for line_B in parallel_B:
		allowed = True
		for line_A in A_partial_solution_lines:
			if len(set(line_A) & set(line_B)) != 1: # lines intersect at exactly one point
				allowed = False
				break
		if allowed:
			intersecting_B.append(line_B)

	return intersecting_A, intersecting_B