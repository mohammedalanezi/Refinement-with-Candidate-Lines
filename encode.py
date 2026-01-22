"""
SAT Instance Encoder
Generates DIMACS CNF encoding file for use in SAT Solvers.

By Mohammed Al-Anezi.
"""

# create a SAT instance class, keeps track of variable and clause count
	# add new variable (building block), returns the variable (var++; return var;) --DONE
	# add clause (building block) (warning when over 100k lines) --DONE
	# add implication clause (building block) --DONE
	# add comment (is added to the clause list with a c in front of it automatically) --DONE
	# forces exactly var_list to have exactly (min to max) true variables --DONE
	# returns variable that is true exactly when var_list has exactly (min to max) true variables --DONE
	
	# string variable for the path to the CNF file ( set_cnf_file(path) ) --DONE
	# set function that changes boolean corresponding to automatically writing to cnf file every X clauses -- DONE
		# by default this is 100k lines and set to true, 
		# only works when cnf path is set, 
		# will warn each time a clause is added when a path is not set and this value is true
	# dump clauses to CNF file (returns false/error if no path is set, otherwise write all clauses to the cnf file and clear clauses but keep variables) -- DONE
	
	# clear clauses --DONE
	# clear variables --DONE
	
	# load from cnf file: -- DONE
		# takes a cnf file as input, 
		# correctly increases clause count and variable count.
	
	# function to mute all warnings or enable all warnings --DONE
		# by default this is set to false (so we have all warnings printing by default) --DONE

	# analyze sat instance: -- NOT YET IMPLEMENTED
		# maximum unique solutions, 
		# clause lengths, 
		# median/mean/mode clause length, 
		# how close it is to each k-Sat critical clause tranisiton value, 
		# etc.

import os
import shutil
from typing import List
from io import StringIO

WARNING_COUNT = 50000

def prepend_to_file_with_temp(filepath, content_to_prepend, skip_first_line):
	temp_filepath = filepath + ".tmp"
	with open(temp_filepath, 'w') as temp:
		temp.write(content_to_prepend)
		with open(filepath, 'r') as f:
			if skip_first_line:
				f.readline()
			shutil.copyfileobj(f, temp, length=1024*1024)  # 1MB buffer
	os.replace(temp_filepath, filepath) # replaces original file with temporary one

class SATEncoder:
	"""Encodes SAT instance in DIMACS CNF clauses."""
	
	def __init__(self, label : str = "un-named", warning_bool : bool = True, clauses_to_write : int = -1, encoding_path : str = None, use_pipe : bool = False):
		self.label = label
		self.var_counter = 0
		self.clause_counter = 0
		self.clauses: List[List[int]] = []
		self.comments: List[str] = []
		
		self.clauses_to_write = clauses_to_write
		self.current_clause_count = 0

		self.encoding_path = encoding_path
		self.display_warnings = warning_bool
		
		self.use_pipe = use_pipe
		self.pipe_buffer = StringIO() if use_pipe else None
		
	def __str__(self) -> str:
		"""Return string representation of SAT Instance."""
		if self.use_pipe:
			return f"{self.label} is a SAT instance with {self.var_counter} variables and {self.clause_counter} clauses, using in-memory pipe."
		return f"{self.label} is a SAT instance with {self.var_counter} variables and {self.clause_counter} clauses" + (f", dumping encoding content to {self.encoding_path}." if self.encoding_path else ".")
	
	def set_warning(self, warning_bool : bool = True):
		"""Enable and Disable warning messages."""
		self.display_warnings = warning_bool

	def _check_warnings(self):
		if self.display_warnings:
			if len(self.clauses) >= WARNING_COUNT or len(self.comments) >= WARNING_COUNT:
				if len(self.clauses) >= WARNING_COUNT:
					print(f"WARNING: Currently there are {len(self.clauses)} clauses, recommended that you dump to a file.")
				if len(self.comments) >= WARNING_COUNT:
					print(f"WARNING: Currently there are {len(self.comments)} comments, recommended that you dump to a file.")
			elif len(self.clauses) + len(self.comments) >= WARNING_COUNT:
				print(f"WARNING: Currently there are {len(self.clauses) + len(self.comments)} comments and clauses, recommended that you dump to a file.")
	
	def enable_pipe_mode(self):
		"""Enable pipe mode for in-memory encoding."""
		self.use_pipe = True
		if self.pipe_buffer is None:
			self.pipe_buffer = StringIO()
	
	def disable_pipe_mode(self):
		"""Disable pipe mode."""
		self.use_pipe = False
		if self.pipe_buffer:
			self.pipe_buffer.close()
			self.pipe_buffer = None
	
	def get_pipe_content(self) -> str:
		"""Get the current content from the pipe buffer."""
		if not self.use_pipe or self.pipe_buffer is None:
			return ""
		return self.pipe_buffer.getvalue()
	
	def clear_pipe(self):
		"""Clear the pipe buffer."""
		if self.pipe_buffer:
			self.pipe_buffer.close()
			self.pipe_buffer = StringIO()

	def set_encoding_path(self, encoding_path : str = "encoding.cnf", clauses_to_write : int = 10000, reload : bool = False):
		"""Set path to dump SAT clauses to file instead of storing in self.clauses."""
		self.encoding_path = encoding_path
		if encoding_path:
			self.clauses_to_write = max(clauses_to_write, 0)
		if reload:
			with open(self.encoding_path, "r") as f:
				line = f.readline()
				line = line.strip()[5:].split()
				self.var_counter = line[0]
				self.clause_counter = line[1]

	def _increment_encoding_count(self):
		self.current_clause_count += 1
		if self.encoding_path and self.clauses_to_write >= 0:
			if self.clauses_to_write <= self.current_clause_count:
				self.dump_encoding() 
	
	def _write_to_pipe(self):
		"""Write current clauses and comments to pipe buffer."""
		if not self.pipe_buffer:
			return
		
		for c in self.comments:
			self.pipe_buffer.write("c " + c + "\n")
		for c in self.clauses:
			clause = " ".join(map(str, c))
			self.pipe_buffer.write(clause + " 0\n")
		
		self.clear_comments()
		self.clear_clauses()
		self.current_clause_count = 0

	def new_variable(self) -> int:
		"""Allocate a new SAT variable."""
		self.var_counter += 1
		return self.var_counter
	
	def add_clause(self, literals: List[int]):
		"""Add a clause to the encoding."""
		if literals:  # Don't add empty clauses
			self.clauses.append(literals)
			self.clause_counter += 1
			self._check_warnings()
			self._increment_encoding_count()
				
	def add_comment(self, comment: str):
		"""Add a comment for the DIMACS output."""
		if comment:
			self.comments.append(comment)
			self._check_warnings()
			self._increment_encoding_count()
	
	def clear_clauses(self):
		"""Clear all clauses in the encoding."""
		self.clauses.clear()
	
	def clear_comments(self):
		"""Clear all comments in the encoding."""
		self.comments.clear()
		
	def add_implication_clause(self, antecedent : List[int], consequent : List[int]): # conjunction(AND) of all antecedental variables implies the disjunction(OR) of consequental variables, e.g. "x1 and .. and xn" implies "y1 or ... or yn"
		"""Add an implication clause to the encoding."""
		for i in range(len(antecedent)):
			antecedent[i] = -antecedent[i]
		self.add_clause(antecedent + consequent)
		return True
	
	def add_forced_cardinality_clause(self, variables : List[int], minimum : int, maximum : int): # <= maximum variables and >= minimum values are true (latin squares would use minimum = maximum = 1 for each symbol)
		"""
		Add cardinality constraint: min_count <= sum(vars) <= max_count
		Uses sequential counter encoding for efficiency.
		"""
		n = len(variables) # rows
		k = maximum + 1	   # columns
		l = minimum
		
		s = [] # Boolean counter variables, s[i][j] says at least j of the variables x1, ..., xi are assigned to true
		for i in range(n + 1):
			row = []
			for j in range(k + 1):
				row.append(self.new_variable())
			s.append(row)
		
		for i in range(n+1):
			self.add_clause([s[i][0]]) # 0 variables are always true of variables [x1, ..., xi]
		for j in range(1, k+1):
			self.add_clause([-s[0][j]]) # j>=1 of nothing is always false
		for j in range(1, l+1):
			self.add_clause([s[n][j]]) # at least minimum of [x0, ..., xi-1] are true
		for i in range(1, n+1):
			self.add_clause([-s[i][k]]) # at most maximum of [x0, ..., xi-1] are true
			
		for i in range(1, n+1): # for each variable xi, propagate counts across the table
			for j in range(1, k+1):
				self.add_implication_clause([s[i-1][j]], [s[i][j]]) # If at least j of the first i-1 variables are true, then at least j of the first i variables are true
				self.add_implication_clause([variables[i-1], s[i-1][j-1]], [s[i][j]]) # If xi is true and at least j-1 of the first i-1 variables are true, then at least j of the first i variables are true
				if j <= l:
					self.add_implication_clause([s[i][j]], [s[i-1][j], variables[i-1]]) # If at least j of the first i variables are true, then either xi is true or at least j of the first i-1 variables were already true
					self.add_implication_clause([s[i][j]], [s[i-1][j-1]]) # If at least j of the first i variables are true, then at least j-1 of the first i-1 variables must be true

	def add_auxiliary_cardinality_clause(self, variables : List[int], minimum : int, maximum : int) -> int:
		"""
		Create an auxiliary variable E that is true iff exactly k of vars_list are true.
		"""
		n = len(variables)
		k = maximum + 1
		l = minimum
		
		s = [[self.new_variable() for _ in range(k + 1)] for _ in range(n + 1)]
		
		for i in range(n + 1):
			self.add_clause([s[i][0]]) # 0 variables are always true of variables [x1, ..., xi]
		for j in range(1, k + 1):
			self.add_clause([-s[0][j]]) # j>=1 of nothing is always false
		
		for i in range(1, n+1): # for each variable xi, propagate counts across the table
			for j in range(1, k+1):
				self.add_implication_clause([s[i-1][j]], [s[i][j]]) # If at least j of the first i-1 variables are true, then at least j of the first i variables are true
				self.add_implication_clause([variables[i-1], s[i-1][j-1]], [s[i][j]]) # If xi is true and at least j-1 of the first i-1 variables are true, then at least j of the first i variables are true
				
				self.add_implication_clause([s[i][j]], [s[i-1][j], variables[i-1]]) # If at least j of the first i variables are true, then either xi is true or at least j of the first i-1 variables were already true
				self.add_implication_clause([s[i][j]], [s[i-1][j-1]]) # If at least j of the first i variables are true, then at least j-1 of the first i-1 variables must be true
		
		E = self.new_variable()
		self.add_implication_clause([E], [s[n][l]]) # E -> "at least minimum"
		self.add_implication_clause([E], [-s[n][k]]) # E -> "not at least maximum+1"
		self.add_implication_clause([s[n][l], -s[n][k]], [E]) # (at least min AND not at least max+1) -> E
		return E

	def _encode_xor(self, vars: List[int]) -> int:
		"""
		Encode XOR of multiple variables using auxiliary variables.
		Returns variable representing the XOR result.
		"""
		if len(vars) == 0: # XOR of nothing is 0, return a fresh var and force it to 0
			result = self.new_variable()
			self.add_clause([-result])
			return result
		elif len(vars) == 1:
			return vars[0]
		elif len(vars) == 2: # XOR of two variables
			return self._encode_xor_pair(vars[0], vars[1])
		else: # Chain XOR operations, better methods exist which I have done before, but they are complex so left for Future work
			result = self._encode_xor_pair(vars[0], vars[1])
			for i in range(2, len(vars)):
				result = self._encode_xor_pair(result, vars[i])
			return result
	
	def _encode_xor_pair(self, a: int, b: int) -> int:
		"""
		Encode XOR of two variables: result = a XOR b
		Returns variable representing a XOR b.
		"""
		result = self.new_variable() # result = a XOR b means: result is true iff exactly one of a, b is true
		# CNF clauses: (a OR b OR NOT result) AND (NOT a OR NOT b OR NOT result) AND (a OR NOT b OR result) AND (NOT a OR b OR result)
		self.add_clause([a, b, -result])
		self.add_clause([-a, -b, -result])
		self.add_clause([a, -b, result])
		self.add_clause([-a, b, result])
		
		return result
	
	def encode_lexicographic_ordering(self, skip_columns: int = 0):
		"""
		Add lexicographic ordering between rows to break symmetry.
		Row i should be lexicographically <= row i+1.
		"""
		self.add_comment("Lexicographic ordering for symmetry breaking")
		
		for i in range(self.k - 1):
			row1 = self.G[i][skip_columns:]
			row2 = self.G[i + 1][skip_columns:]
			self._add_lex_order_constraint(row1, row2)

	def _add_lex_order_constraint(self, row1: List[int], row2: List[int]):
		"""
		Encode row1 <=_lex row2 using auxiliary equality variables.
		"""
		n = len(row1)
		
		# Create auxiliary variables for prefix equality: eq_prefix[j] means rows are equal in the first j columns
		eq_prefix = [self.new_variable() for _ in range(n + 1)]
		
		self.add_clause([eq_prefix[0]]) # Base case: rows are equal in 0 columns (always true)
		
		for j in range(n): # Encode: eq_prefix[j+1] <=> eq_prefix[j] AND (row1[j] == row2[j])
			# If eq_prefix[j+1] is true, then eq_prefix[j] must be true
			self.add_clause([-eq_prefix[j+1], eq_prefix[j]])
			
			# If eq_prefix[j+1] is true, then row1[j] == row2[j]
			self.add_clause([-eq_prefix[j+1], -row1[j], row2[j]]) # row1[j] implies row2[j]
			self.add_clause([-eq_prefix[j+1], row1[j], -row2[j]]) # row2[j] implies row1[j]
			
			# If eq_prefix[j] is true and row1[j] == row2[j], then eq_prefix[j+1] is true
			# We need two cases for row1[j] == row2[j]:
			self.add_clause([-eq_prefix[j], -row1[j], -row2[j], eq_prefix[j+1]]) # both 1
			self.add_clause([-eq_prefix[j], row1[j], row2[j], eq_prefix[j+1]]) # both 0
			
			# Lexicographic constraint: if rows are equal up to column j, then row1 cannot have 1 where row2 has 0 at column j
			self.add_clause([-eq_prefix[j], -row1[j], row2[j]])
	
	def to_dimacs(self) -> str | bool:
		"""Generate DIMACS CNF format output."""
		if self.use_pipe:
			# finalize any remaining content
			if self.clauses or self.comments:
				self._write_to_pipe()
			
			content = self.get_pipe_content() # get buffered content
			
			# Prepare header
			lines = []
			lines.append(f"c {self.label} SAT Encoding")
			lines.append(f"c Variables: {self.var_counter}")
			lines.append(f"c Clauses: {self.clause_counter}")
			lines.append("c")
			lines.append(f"p cnf {self.var_counter} {self.clause_counter}")
			
			return '\n'.join(lines) + '\n' + content
		
		if self.encoding_path:
			print(f"SAT instance has been dumped to {self.encoding_path}.")
			return False
		
		lines = []
		
		# add comments so all information is self contained
		lines.append(f"c {self.label} SAT Encoding")
		lines.append(f"c Variables: {self.var_counter}")
		lines.append(f"c Clauses: {len(self.clauses)}")
		lines.append("c")
		for comment in self.comments:
			lines.append(f"c {comment}")
		lines.append("c") # end of comments
		
		lines.append(f"p cnf {self.var_counter} {self.clause_counter}") # header line required for DIMCAS format
		
		for clause in self.clauses: # Clauses
			lines.append(' '.join(map(str, clause)) + ' 0')
		
		return '\n'.join(lines)
	
	def finalize_encoding(self):
		"""
		Dump reminaing clauses and comments into self.encoding_path then add DIMACS CNF header.
		
		Returns nothing.
		"""
		if self.use_pipe: # in pipe mode, just ensure everything is written
			if self.clauses or self.comments:
				self._write_to_pipe()
			return
		
		self.dump_remaining_encoding()
		skip_first = False
		with open(self.encoding_path, "r") as f:
			if "p cnf" in f.readline():
				skip_first = True
		prepend_to_file_with_temp(self.encoding_path, f"p cnf {self.var_counter} {self.clause_counter}\n", skip_first) 

	def dump_encoding(self):
		"""Dump current clauses and comments into self.encoding_path."""
		if self.use_pipe:
			self._write_to_pipe()
			return
		
		if self.display_warnings:
			print("Dumping clauses and comments.")
		self.current_clause_count = 0
		with open(self.encoding_path, "a") as f:
			for c in self.comments:
				f.write("c " + c + "\n")
			for c in self.clauses:
				clause = ""
				for v in c:
					clause += str(v) + " "
				f.write(clause + "0\n")
			self.clear_comments()
			self.clear_clauses()
		
	def dump_remaining_encoding(self):
		"""Dump reminaing clauses and comments into self.encoding_path."""
		if self.use_pipe:
			self._write_to_pipe()
			return
		
		if self.current_clause_count > 0:
			self.current_clause_count = self.clauses_to_write
			self._increment_encoding_count()

# Run encoding in a SAT Solver and save output, then proceed to decode.py