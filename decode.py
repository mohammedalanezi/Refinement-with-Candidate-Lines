"""
SAT Solution Decoder for SAT instances
Parses SAT solver output and gives us easy to use functions to extract information.

By Mohammed Al-Anezi.
"""

# function that takes in satsolver, input.cnf, output.txt, and arguments -- DONE
	# runs input.cnf into sat solver with arguments
	# passes sat solver's output into output.txt
	# returns WALL TIME to run the sat instance (can use the functions mentioned below to get the rest of the info)

# all functions that take output.txt as input:
	# get satisfiability -- DONE
	# get variable assignment -- DONE
		# uses previous: get TRUE variable assignment
		# uses previous: get FALSE variable assignment
	# get timings from the file -- DONE

import subprocess
import time
from io import StringIO

class SATDecoder:
	"""Used to get data from a SAT instance's SAT Solver solutions."""
	
	def __init__(self, file_path : str = None, parse_function = None, use_pipe : bool = False, pipe_content : str = None):
		"""
		Initialize with a SAT encoding.
		
		Args:
			file_path: path the SAT Solver's output file (string)
			parse_function: the string representation of the parsed solution (function)
		"""
		self.file_path = file_path
		self.parse_function = parse_function
		
		self.use_pipe = use_pipe
		self.pipe_buffer = StringIO(pipe_content) if use_pipe and pipe_content else (StringIO() if use_pipe else None)

		self.timings = {}
		self.solution_count = -1
	
	def __str__(self) -> str:
		"""Return string representation of the SAT solution."""
		return self.parse_function(self)
	
	def enable_pipe_mode(self, initial_content : str = None):
		"""Enable pipe mode for in-memory processing."""
		self.use_pipe = True
		if self.pipe_buffer is None:
			self.pipe_buffer = StringIO(initial_content) if initial_content else StringIO()
	
	def disable_pipe_mode(self):
		"""Disable pipe mode."""
		self.use_pipe = False
		if self.pipe_buffer:
			self.pipe_buffer.close()
			self.pipe_buffer = None
	
	def set_pipe_content(self, content : str):
		"""Set the content of the pipe buffer."""
		if self.pipe_buffer:
			self.pipe_buffer.close()
		self.pipe_buffer = StringIO(content)
		self.use_pipe = True
	
	def get_pipe_content(self) -> str:
		"""Get the current content from the pipe buffer."""
		if not self.use_pipe or self.pipe_buffer is None:
			return ""
		current_pos = self.pipe_buffer.tell()
		self.pipe_buffer.seek(0)
		content = self.pipe_buffer.read()
		self.pipe_buffer.seek(current_pos)
		return content
	
	def clear_pipe(self):
		"""Clear the pipe buffer."""
		if self.pipe_buffer:
			self.pipe_buffer.close()
			self.pipe_buffer = StringIO()
	
	def _get_lines(self):
		"""Internal method to get lines from either file or pipe."""
		if self.use_pipe and self.pipe_buffer:
			self.pipe_buffer.seek(0)
			return self.pipe_buffer.readlines()
		elif self.file_path:
			with open(self.file_path, 'r') as f:
				return f.readlines()
		return []
	
	def run_sat_solver(self, sat_solver_path : str = None, input_path : str = None, arguments : str = [], 
					display_to_console : bool = False, on_solution_found = None, input_content : str = None, track_solution_count : bool = True, track_timings : bool = True) -> float | None:
		"""
		Runs SAT instance through a specified SAT Solver with a specified Input file and outputs it to our Output file.
		
		Args:
			sat_solver_path: Path to SAT solver executable
			input_path: Path to input CNF file
			arguments: List of command-line arguments for the solver
			display_to_console: Whether to display output to console
			on_solution_found: Callback function called each time a solution is found (for exhaustive solving)
		
		Returns:
			WALL Time of Solver (float)
		"""
		if not sat_solver_path:
			print(f"WARNING: No SAT solver path provided.")
			return None
		
		if not input_path and not input_content:
			print(f"WARNING: No input path or content provided.")
			return None
			
		if track_solution_count:
			self.solution_count = 0
		if track_timings:
			self.timings = {}
		
		wall_time = time.time()
		
		if input_content: # use entire dimcas input
			commands = [sat_solver_path]
			
			if not input_path:
				commands.append('-') 
			else:
				commands.append(input_path)
			
			commands += arguments
			
			process = subprocess.Popen(
				commands,
				stdin=subprocess.PIPE,
				stdout=subprocess.PIPE,
				stderr=subprocess.STDOUT,
				text=True
			)
			
			if self.use_pipe:
				if self.pipe_buffer:
					self.pipe_buffer.close()
				self.pipe_buffer = StringIO()
			
			def write_stdin():
				try:
					process.stdin.write(input_content)
					process.stdin.close()
				except:
					pass
			
			write_stdin()
			
			for line in process.stdout: # read output
				if display_to_console:
					print(line, end="", flush=True)
				
				if self.use_pipe:
					self.pipe_buffer.write(line)
				elif self.file_path:
					with open(self.file_path, "a") as out_file:
						out_file.write(line)
				
				self._process_sat_output(line)
				
			process.stdout.close()
			process.wait()
			
		elif self.use_pipe: # pipe mode with file input then capture output in memory
			commands = [sat_solver_path, input_path] + arguments

			process = subprocess.Popen(
				commands,
				stdout=subprocess.PIPE,
				stderr=subprocess.STDOUT,
				text=True
			)
			
			if self.pipe_buffer: # clear and prepare pipe buffer
				self.pipe_buffer.close()
			self.pipe_buffer = StringIO()
			
			for line in process.stdout:
				if display_to_console:
					print(line, end="", flush=True)
				self.pipe_buffer.write(line)
				
				self._process_sat_output(line)
			
			process.stdout.close()
			process.wait()
			
		elif self.file_path: # file mode (write to file)
			with open(self.file_path, "w") as out_file:
				if not on_solution_found and not display_to_console:
					commands = [sat_solver_path, input_path] + arguments
					
					process = subprocess.run(
						commands,
						stdout=out_file,
						stderr=subprocess.STDOUT
					)
				else:
					commands = [sat_solver_path, input_path] + arguments
					
					process = subprocess.Popen(
						commands,
						stdout=subprocess.PIPE,
						stderr=subprocess.STDOUT,
						text=True
					)

					for line in process.stdout:
						if display_to_console:
							print(line, end="", flush=True)
						out_file.write(line)

						self._process_sat_output(line)

					process.stdout.close()
					process.wait()
		else:
			print(f"WARNING: No output path or pipe mode enabled.")
			return None
		
		return round((time.time() - wall_time) * 1000)/1000
	
	def get_timings(self) -> dict[str, float]:
		"""
		Parse SAT solver output to get all the timings of the SAT instance.
		
		Returns:
			List of timings (float variables)
		"""
		
		timings = {}

		with open(self.file_path, 'r') as f:
			for line in f:
				line = line.strip()
				if line.startswith('c process-time:'):
					timings["process-time"] = line.split()[-2]
				if line.startswith('c finished parsing after'):
					timings["parse-time"] = line.split()[-2]
				if line.startswith("c total process time since initialization:"):
					timings['process-time-since-initialization'] = line.split()[6]
				if line.startswith("c total real time since initialization:"):
					timings['initialization-real-time-total'] = line.split()[6]
					
				clause_info = self._parse_clause_line(line)
				if clause_info:
					clauses, parse_time = clause_info
					self.timings["parse-clause-count"] = clauses
					self.timings["parsing-time"] = parse_time
		
		return timings
	
	def get_satisfiability(self) -> bool | None:
		"""
		Parse SAT solver output to get if we have SAT or UNSAT.
		
		Returns:
			Boolean output, TRUE = SAT, FALSE = UNSAT
		"""
		
		with open(self.file_path, 'r') as f:
			for line in f:
				line = line.strip()
				if ("SATISFIABLE" in line) or ("New solution" in line): # sat or exhaustive and at least 1 solution
					return True
				if "UNSATISFIABLE" in line:
					return False
		
		return None
	
	def get_variable_assignment(self, positive_only : bool = True) -> list[int]:
		"""
		Parse SAT solver output and extract variable assignments.
		We assume the output file will correctly append "v" to the front of all variable assignments.
		
		Returns:
			List of literals depending on positive_only (satisfied or unsatisfied variables)
		"""
		satisfied = []
		
		with open(self.file_path, 'r') as f:
			for line in f:
				line = line.strip()
				
				if line.startswith('c') or line.startswith('s'): # skip comments and status lines, code not entirely needed
					continue
				
				if line.startswith('v'): # parse variable assignments
					literals = line[1:].strip().split() # remove 'v' prefix and split
					for lit in literals:
						lit_int = int(lit)
						if not positive_only: # only displays "negative" assignments
							lit_int = -lit_int
						if lit_int > 0:
							satisfied.append(lit_int)
						elif lit_int == 0:
							break  # end of assignment
		
		return satisfied

	def get_exhaustive_solutions(self):
		"""
		Parse SAT solver output and extract all solutions.
		We assume the output file will append each solution with "c New solution:" and solution count with "c Number of solutions:".
		
		Returns:
			Number of solutions (int)
			List of solutions (unsatisfied variables)
		"""
		count = -1
		solutions = []

		with open(self.file_path, 'r') as f:
			for line in f:
				if line.startswith("c Number of solutions:"):
					count = line[23:-1]
				elif line.startswith("c New solution:"):
					solutions.append(line[16:-2])
		
		return count, solutions
	
	def _process_sat_output(self, line: str, on_solution_found = None, track_solution_count : bool = True, track_timings : bool = True):
		if on_solution_found and line.startswith("c New solution:"):
			solution_str = line[16:].strip()
			on_solution_found(solution_str)
		
		if track_solution_count and line.startswith('c '):
			val = self._parse_last_value(line)
			if val != -1:
				self.solution_count = val   # update to latest cumulative count

		if track_timings and line.startswith('c '):
			timing = self._parse_timing_line(line)
			if timing:
				key, value = timing
				self.timings[key] = value 

			clause_info = self._parse_clause_line(line)
			if clause_info:
				clauses, parse_time = clause_info
				self.timings["parse-clause-count"] = clauses
				self.timings["parsing-time"] = parse_time

	def _parse_last_value(self, line: str):
		"""
		Parse the last token of a line as a numeric value.
		Returns the number if line has exactly 20 tokens and last token has no '%',
		otherwise returns -1.
		"""
		tokens = line.split()
		if len(tokens) != 20:
			return -1
		last = tokens[-1]
		if '%' in last:
			return -1
		try:
			# Try int first, fallback to float
			return int(last)
		except ValueError:
			try:
				return float(last)
			except ValueError:
				return -1
	
	def _parse_timing_line(self, line: str) -> tuple[str, float] | None:
		"""Extract timing name and value from a line. Returns (key, value) or None."""
		line = line.strip()
		if line.startswith('c process-time:'):
			# line: "c process-time: 0.01 seconds"
			parts = line.split()
			if len(parts) >= 3:
				return ("process-time", float(parts[2]))
		elif line.startswith('c finished parsing after'):
			# line: "c finished parsing after 0.00 seconds"
			parts = line.split()
			if len(parts) >= 5:
				return ("parse-time", float(parts[4]))
		elif line.startswith("c total process time since initialization:"):
			# line: "c total process time since initialization: 0.01 seconds"
			parts = line.split()
			if len(parts) >= 7:
				return ("process-time-since-initialization", float(parts[6]))
		elif line.startswith("c total real time since initialization:"):
			parts = line.split()
			if len(parts) >= 7:
				return ("initialization-real-time-total", float(parts[6]))
		return None
	
	def _parse_clause_line(self, line: str):
		"""
		Extracts clause count and parsing time from a line like: 'c parsed 77372 clauses in 0.04 seconds process time'

		Returns (clause_count (int), time_seconds (float)) or None if no match.
		"""
		line = line.strip()
		# Match pattern: "c parsed <number> clauses in <float> seconds process time"
		if not line.startswith("c parsed "):
			return None
		# Remove the leading "c " and split
		parts = line[2:].split()
		if len(parts) >= 7 and parts[0] == "parsed" and parts[2] == "clauses" and parts[3] == "in" and parts[5] == "seconds":
			try:
				clause_count = int(parts[1])
				time_taken = float(parts[4])
				return clause_count, time_taken
			except (ValueError, IndexError):
				pass
		return None