"""
Helper for my functions that don't belong to either encoding SAT or decoding SAT.

By Mohammed Al-Anezi.
"""

import subprocess
import time
from io import StringIO
from collections import defaultdict

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