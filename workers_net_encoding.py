'''
Workers Net Encoding by Mohammed

Parallel processing version for exhaustive SAT solutions
Processes each A refinement in parallel to find all valid Bs refinements
'''

import threading
import queue  
import os
import sys
import time
from collections import defaultdict
import multiprocessing
from multiprocessing import shared_memory
from functools import partial, lru_cache
import numpy as np

if __name__ == "__main__":
	multiprocessing.set_start_method("spawn", force=True) # not sure what this does but without it my code doesnt reach sat solver

from helpers import *
import encode
import decode
from statistics import PerformanceStats

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)

exhaust = True # set to True for exhaustive + parallel processing

exhaust_satsolver_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical-exhaust")
satsolver_path = os.path.join(parent_dir, "kissat-rel-4.0.2", "build", "kissat")

if len(sys.argv) < 2:
	print("Usage: python3 generate.py <template_id>\n")
	sys.exit(1)

template_id = int(sys.argv[1]) + 1
input_path = os.path.join(script_dir, f"{template_id}-input-wn.cnf")
output_path = os.path.join(script_dir, f"{template_id}-output-wn.txt")
template_path = os.path.join(parent_dir, "refinements and candidate lines", "templates", str(template_id)+"-template.txt")
candidate_lines_2_path = os.path.join(parent_dir, "refinements and candidate lines", "2-candidate_lines", f"{template_id}-candidate_lines.txt")
candidate_lines_3_path = os.path.join(parent_dir, "refinements and candidate lines", "3-candidate_lines", f"{template_id}-candidate_lines.txt")

points = [set(), set()]
candidate_lines = [[], []]
candidate_line_count = [0, 0]
order = 10
k_net = []
mapping = {}
variable_counts = {}
latin_squares = 3

def init_worker(candidate_lines_tuple, candidate_line_count_tuple):
	"""Initialize worker process with shared memory access."""
	global candidate_lines, candidate_line_count
	candidate_lines = candidate_lines_tuple
	candidate_line_count = candidate_line_count_tuple
	
def getIntersectingBCandidateLines(A_candidate_lines):
	possible_B_lines = []
	for j in range(candidate_line_count[1]):
		allowed = True
		for i in range(10):
			if len(set(A_candidate_lines[i]) & set(getLine(j, candidate_lines[1]))) != 1:
				allowed = False
				break
		if allowed:
			possible_B_lines.append(j)
	return possible_B_lines

# worker function for parallel processing of each A solution
def process_A_solution(selected_A, template_id, point_to_B, total_points, exhaust_satsolver_path, script_dir):
	"""
	Process a single A configuration to find all valid B configurations.
	
	Args:
		solution_lines: List of lines containing the solution
		other args are from the main branch
	
	Returns:
		dict with A configuration, list of valid Bs, and metadata
	"""
	try:
		solution_id = hash(str(selected_A)) % 1000000
		wall_time = time.time()

		invalidReturn = {
			'solution_id': solution_id,
			'selected_A': selected_A,
			'num_valid_Bs': 0,
			'valid_Bs': [],
			'wall_time': 0.0,
			'status': 'success'
		}
		
		possible_B_lines = getIntersectingBCandidateLines(selected_A)

		if len(possible_B_lines) < 10:
			invalidReturn['wall_time'] = float(time.time() - wall_time)
			return invalidReturn
		
		# build new SAT instance for finding all valid B configurations
		encoding_secondary = encode.SATEncoder(f"Secondary B search for A-{solution_id}", warning_bool=False, use_pipe=True)
		
		b = {}
		for line in possible_B_lines:
			b[line] = encoding_secondary.new_variable() 
		
		for p in total_points:
			b_indices = point_to_B.get(p, [])
			if b_indices:
				b_lines = [b[i] for i in b_indices if i in possible_B_lines]
				if len(b_lines) > 0:
					encoding_secondary.add_forced_cardinality_clause(b_lines, 1, 1)
				else:
					invalidReturn['wall_time'] = float(time.time() - wall_time)
					return invalidReturn

		encoding_secondary.finalize_encoding()

		def parse_secondary_solution(decoder: decode.SATDecoder) -> str:
			count, _ = decoder.get_exhaustive_solutions()
			return f"Found {count} valid B configurations for A-{solution_id}"
		
		decoding_secondary = decode.SATDecoder(use_pipe=True, parse_function=parse_secondary_solution)
		
		all_b_solution_lines = []
		def collect_b_solution(solution_str):
			all_b_solution_lines.append(solution_str)
		
		valid_Bs = []
		wall_time = decoding_secondary.run_sat_solver(
			exhaust_satsolver_path, 
			input_content=encoding_secondary.to_dimacs(), 
			arguments=["--order", str(len(possible_B_lines))],
			display_to_console=False, 
			on_solution_found=collect_b_solution
		)

		for b_solution_str in all_b_solution_lines:
			selected_B = [possible_B_lines[int(i) - 1] for i in b_solution_str.split()[:10]]
			valid_Bs.append(selected_B)
		
		result = {
			'solution_id': solution_id,
			'selected_A': selected_A,
			'num_valid_Bs': len(valid_Bs),
			'valid_Bs': valid_Bs,
			'wall_time': wall_time,
			'status': 'success'
		}

		return result
		
	except Exception as e:
		import traceback
		return {
			'solution_id': hash(str(selected_A)) % 1000000,
			'status': 'failed',
			'error': str(e),
			'traceback': traceback.format_exc()
		}

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
		
def solutionToCandidateLines(solution : str):
	Q_square = [] 
	candidate_lines = []

	for r in range(order):
		Q_square.append([])
		for c in range(order):
			Q_square[r].append(-1) # easily tells us if logic error occured by the existance of -1 symbol

	for val in solution.split():
		val = int(val)
		if val >= 1 and val <= order ** 3:
			l, r, c, s = get4DIndex(val)
			Q_square[r + l * order][c] = s

	for symbol in range(order):
		candidate_lines.append([])
		for r in range(order):
			for c in range(order):
				if Q_square[r][c] == symbol:
					candidate_lines[symbol].append(get1DIndex(r, c, order))
		
	return candidate_lines

if __name__ == "__main__":
	rewrite = True
		
	print(f"Loading candidate lines for template-{template_id}.")
	candidate_lines[0], points[0], candidate_line_count[0] = load_candidate_lines_file(candidate_lines_2_path)
	candidate_lines[1], points[1], candidate_line_count[1] = load_candidate_lines_file(candidate_lines_3_path)
	total_points = points[0] | points[1]
	point_to_A = pointsToLine(candidate_lines[0], candidate_line_count[0])
	point_to_B = pointsToLine(candidate_lines[1], candidate_line_count[1])
	
	encoding = encode.SATEncoder("4-NET(10) Encoding with Auxiliary Matrix for Template Refinement", False)
	
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

	if rewrite:
		open(input_path, "w").close()
		encoding.set_encoding_path(input_path, 10000, False)

		Q, Z, P = k_net[0], k_net[1], k_net[2]
		exhaustive_variables = variable_counts[0] #encoding.var_counter # A refinement

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

		print("Writing latin square constraints.") #  move the bulk of this to encode.py since it will be reused a lot
		for index in range(latin_squares): # Maintain latin square clauses
			square = [P, Q, Z][index]
			encodeLatinSquare(encoding, square)
					
		print("Writing orthogonality constraints.")
		encodeMyrvoldOrthogonality(encoding, P, Q, Z)

		encoding.finalize_encoding()
		print(encoding)
	exhaustive_variables = 10 * 10 * 10 # 10 rows, 10 columns, 10 symbols 

	current_time = time.time()

	if exhaust: 
		try:
			perf_stats = PerformanceStats()

			worker = partial( # set up worker function with fixed arguments
				process_A_solution,
				template_id=template_id,
				point_to_B=point_to_B,
				total_points=total_points,
				exhaust_satsolver_path=exhaust_satsolver_path,
				script_dir=script_dir
			)

			num_proc = max(multiprocessing.cpu_count() - 2, 1) # limit number of processes to avoid resource exhaustion
			print(f"Using {num_proc} CPU cores for parallel processing.")
			
			solution_queue = queue.Queue()
			results_list = []
			shutdown_event = threading.Event()

			def stats_display():
				"""Periodically display performance statistics."""
				while not shutdown_event.is_set():
					time.sleep(15.0)  # Update every 15 seconds
					perf_stats.snapshot_rates()
					
					summary = perf_stats.get_summary()
					print(f"\n{'='*70}")
					print(f"PERFORMANCE STATS (Elapsed: {summary['elapsed_time']:.1f}s); template-{template_id}")
					print(f"{'='*70}")
					print(f"Counts: Raw A: {summary['counts']['raw_A']} | "
						  f"Processed A: {summary['counts']['processed_A']} | "
						  f"Total B: {summary['counts']['total_B']}")
					print(f"\nCurrent Rates (60s window):")
					print(f"  Raw A:       {summary['current_rates']['raw_A_rate']:.2f} A/s")
					print(f"  Processed A: {summary['current_rates']['processed_A_rate']:.2f} A/s")
					print(f"  B configs:   {summary['current_rates']['B_rate']:.2f} B/s")
					print(f"\nOverall Rates (since start):")
					print(f"  Raw A:       {summary['overall_rates']['raw_A']:.2f} A/s")
					print(f"  Processed A: {summary['overall_rates']['processed_A']:.2f} A/s")
					print(f"  B configs:   {summary['overall_rates']['B']:.2f} B/s")
					print(f"\n60s Window Stats (Top/Avg/Bottom):")
					print(f"  Raw A:       {summary['rate_stats_60s']['raw_A']['top']:.2f} / "
						  f"{summary['rate_stats_60s']['raw_A']['avg']:.2f} / "
						  f"{summary['rate_stats_60s']['raw_A']['bottom']:.2f} A/s")
					print(f"  Processed A: {summary['rate_stats_60s']['processed_A']['top']:.2f} / "
						  f"{summary['rate_stats_60s']['processed_A']['avg']:.2f} / "
						  f"{summary['rate_stats_60s']['processed_A']['bottom']:.2f} A/s")
					print(f"  B configs:   {summary['rate_stats_60s']['B']['top']:.2f} / "
						  f"{summary['rate_stats_60s']['B']['avg']:.2f} / "
						  f"{summary['rate_stats_60s']['B']['bottom']:.2f} B/s")
					print(f"\n60s Window Raw Stats (Top/Avg/Bottom):")
					print(f"  Raw A:       {summary['raw_rate_stats_60s']['raw_A']['top']:.2f} / "
						  f"{summary['raw_rate_stats_60s']['raw_A']['avg']:.2f} / "
						  f"{summary['raw_rate_stats_60s']['raw_A']['bottom']:.2f} A/s")
					print(f"  Processed A: {summary['raw_rate_stats_60s']['processed_A']['top']:.2f} / "
						  f"{summary['raw_rate_stats_60s']['processed_A']['avg']:.2f} / "
						  f"{summary['raw_rate_stats_60s']['processed_A']['bottom']:.2f} A/s")
					print(f"  B configs:   {summary['raw_rate_stats_60s']['B']['top']:.2f} / "
						  f"{summary['raw_rate_stats_60s']['B']['avg']:.2f} / "
						  f"{summary['raw_rate_stats_60s']['B']['bottom']:.2f} B/s")
					print(f"{'='*70}\n")
					
			stats_thread = threading.Thread(target=stats_display, daemon=True)
			stats_thread.start()

			def on_solution_found(solution):
				"""Called by run_sat_solver each time a new solution is found."""
				candidate_lines = solutionToCandidateLines(solution)
				solution_queue.put(candidate_lines)
				perf_stats.record_raw_A()

			def solution_processor():
				"""Process solutions from queue and submit to pool."""
				try:
					with multiprocessing.Pool(processes=num_proc, initializer=init_worker, initargs=(tuple(candidate_lines),tuple(candidate_line_count),)) as local_pool:
						pending_results = []
						
						while not shutdown_event.is_set():
							try:																
								solution = solution_queue.get(timeout=1) # A refinement
								if solution is None:
									break
								async_result = local_pool.apply_async(worker, (solution,)) # assign processor to A refinement
								pending_results.append(async_result) # add to tracking list of "currently being worked on A refinement"

								completed = []
								for i, async_res in enumerate(pending_results): # check for completed results
									if async_res.ready(): # is "currently being worked on A refinement" done?
										try:
											result = async_res.get() # result of A refinement
											results_list.append(result)
											if result['status'] == 'success':
												perf_stats.record_processed_A(result['num_valid_Bs'])
											completed.append(i)
										except Exception as e:
											print(f"Error getting result: {e}")
											completed.append(i)
								
								for i in reversed(completed):
									pending_results.pop(i) # remove all completed refinements from pending list

							except queue.Empty:
								continue
							except Exception as e:
								print(f"ERROR in solution_processor loop: {e}")
								import traceback
								traceback.print_exc()
								continue
						
						print(f"Waiting for {len(pending_results)} pending results...")
						for async_res in pending_results: # wait for all remaining results
							try:
								result = async_res.get(timeout=60)
								results_list.append(result)
								
								if result['status'] == 'success':
									perf_stats.record_processed_A(result['num_valid_Bs'])
							except Exception as e:
								print(f"Error getting final result: {e}")
				except Exception as e:
					print(f"CRITICAL ERROR in solution_processor: {e}")
					import traceback
					traceback.print_exc()

			processor_thread = threading.Thread(target=solution_processor, daemon=False)
			processor_thread.start()

			try:
				decoding = decode.SATDecoder(output_path, parseSolution)
				print(f"Running SAT Solver on {input_path}.")

				wall_time = decoding.run_sat_solver(
					exhaust_satsolver_path, 
					input_path,
					["--only-neg", "--order", str(exhaustive_variables)],
					False,
					on_solution_found=on_solution_found
				)
				
				count, _ = decoding.get_exhaustive_solutions()
				print(f"\nFound {count} A configurations total. Waiting for all to be processed...")
			finally:
				solution_queue.put(None)
				processor_thread.join(timeout=600)
				if processor_thread.is_alive():
					print("WARNING: Processor thread did not finish in time")
					shutdown_event.set()
					processor_thread.join(timeout=60)

			performance_path = os.path.join(script_dir, f"{template_id}-performance-stats.txt")
			with open(performance_path, 'w') as f: # write final results
				final_summary = perf_stats.get_summary()
				f.write(f"\n{'='*70}")
				f.write(f"FINAL PERFORMANCE SUMMARY")
				f.write(f"{'='*70}")
				f.write(f"Total Runtime: {final_summary['elapsed_time']:.2f}s")
				f.write(f"\nFinal Counts:")
				f.write(f"  Raw A configurations found:     {final_summary['counts']['raw_A']}")
				f.write(f"  Processed A configurations:     {final_summary['counts']['processed_A']}")
				f.write(f"  Total B configurations found:   {final_summary['counts']['total_B']}")
				f.write(f"\nOverall Average Rates:")
				f.write(f"  Raw A:       {final_summary['overall_rates']['raw_A']:.3f} A/s")
				f.write(f"  Processed A: {final_summary['overall_rates']['processed_A']:.3f} A/s")
				f.write(f"  B configs:   {final_summary['overall_rates']['B']:.3f} B/s")
				f.write(f"\n60-Second Window Statistics (Top/Avg/Bottom):")
				f.write(f"  Raw A:       {final_summary['rate_stats_60s']['raw_A']['top']:.2f} / "
					f"{final_summary['rate_stats_60s']['raw_A']['avg']:.2f} / "
					f"{final_summary['rate_stats_60s']['raw_A']['bottom']:.2f} A/s")
				f.write(f"  Processed A: {final_summary['rate_stats_60s']['processed_A']['top']:.2f} / "
					f"{final_summary['rate_stats_60s']['processed_A']['avg']:.2f} / "
					f"{final_summary['rate_stats_60s']['processed_A']['bottom']:.2f} A/s")
				f.write(f"  B configs:   {final_summary['rate_stats_60s']['B']['top']:.2f} / "
					f"{final_summary['rate_stats_60s']['B']['avg']:.2f} / "
					f"{final_summary['rate_stats_60s']['B']['bottom']:.2f} B/s")
				f.write(f"\n60-Second Window Raw Statistics (Top/Avg/Bottom):")
				f.write(f"  Raw A:       {final_summary['raw_rate_stats_60s']['raw_A']['top']:.2f} / "
					f"{final_summary['raw_rate_stats_60s']['raw_A']['avg']:.2f} / "
					f"{final_summary['raw_rate_stats_60s']['raw_A']['bottom']:.2f} A/s")
				f.write(f"  Processed A: {final_summary['raw_rate_stats_60s']['processed_A']['top']:.2f} / "
					f"{final_summary['raw_rate_stats_60s']['processed_A']['avg']:.2f} / "
					f"{final_summary['raw_rate_stats_60s']['processed_A']['bottom']:.2f} A/s")
				f.write(f"  B configs:   {final_summary['raw_rate_stats_60s']['B']['top']:.2f} / "
					f"{final_summary['raw_rate_stats_60s']['B']['avg']:.2f} / "
					f"{final_summary['raw_rate_stats_60s']['B']['bottom']:.2f} B/s")
				f.write(f"{'='*70}\n")

			results_path = os.path.join(script_dir, f"{template_id}-all-AB-pairs.txt")
			with open(results_path, 'w') as f: # write final results
				f.write(f"Template {template_id} - Complete A-B Configuration Results\n")
				f.write(f"Successfully processed: {len([r for r in results_list if r['status'] == 'success'])}\n\n")
				
				total_AB_pairs = 0
				maximum_printed_squares = -1
				for result in results_list:
					if result['status'] == 'success':
						total_AB_pairs += result['num_valid_Bs']
						f.write(f"A-{result['solution_id']}:\n")
						f.write(f"  Refined A Latin Square: {result['selected_A']}\n")
						f.write(f"  Number of valid Bs: {result['num_valid_Bs']}\n")
						f.write(f"  Processing time: {result['wall_time']:.2f}s\n")
						
						if result['num_valid_Bs'] > 0 and result['num_valid_Bs'] <= maximum_printed_squares or maximum_printed_squares < 0:
							for idx, b_config in enumerate(result['valid_Bs']):
								f.write(f"    B{idx+1}: {b_config}\n")
						elif result['num_valid_Bs'] > maximum_printed_squares and maximum_printed_squares > 0:
							for idx, b_config in enumerate(result['valid_Bs'][:5]):
								f.write(f"    B{idx+1}: {b_config}\n")
							f.write(f"    ... and {result['num_valid_Bs'] - 5} more\n")
						f.write("\n")
				
				f.write(f"\nTotal valid (A, B) pairs found: {total_AB_pairs}\n")

			print(f"All results written to {results_path}")
			print(f"Total valid (A, B) pairs: {total_AB_pairs}")
		finally: # clean up shared memory
			print("Shared memory cleaned up")
	
	else: # non-exhaustive mode
		decoding = decode.SATDecoder(output_path, parseSolution)
		wall_time = decoding.run_sat_solver(satsolver_path, input_path, [], True)
		print("\n" + str(decoding))
