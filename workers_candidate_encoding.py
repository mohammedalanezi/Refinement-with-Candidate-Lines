'''
Workers Candidate Encoding by Mohammed

Parallel processing version for exhaustive SAT solutions
Processes each A refinement in parallel to find all valid Bs refinements

Code is not the best! This is my first time doing parallel processing in Python!
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

import encode
import decode

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)

exhaust = True # set to True for exhaustive + parallel processing

exhaust_satsolver_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical-exhaust")
satsolver_path = os.path.join(parent_dir, "kissat-rel-4.0.2", "build", "kissat")

if len(sys.argv) < 2:
	print("Usage: python3 generate.py <template_id>\n")
	sys.exit(1)

template_id = int(sys.argv[1]) + 1
input_path = os.path.join(script_dir, f"{template_id}-input-wc.cnf")
output_path = os.path.join(script_dir, f"{template_id}-output-wc.txt")
candidate_lines_2_path = os.path.join(parent_dir, "refinements and candidate lines", "2-candidate_lines", f"{template_id}-candidate_lines.txt")
candidate_lines_3_path = os.path.join(parent_dir, "refinements and candidate lines", "3-candidate_lines", f"{template_id}-candidate_lines.txt")

points = [set(), set()]
candidate_lines = [[[], []], [[], []]]
candidate_line_count = [0, 0]
order = 10

AB_intersection = []
A_sets = []
B_sets = []

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

# global variables for worker processes
_shm = None
_AB_intersection = None
_candidate_line_count = None

def init_worker(shm_name, shape, candidate_line_count_tuple):
	"""Initialize worker process with shared memory access."""
	global _shm, _AB_intersection, _candidate_line_count
	try:
		_shm = shared_memory.SharedMemory(name=shm_name)
		_AB_intersection = np.ndarray(shape, dtype=np.int8, buffer=_shm.buf)
		_candidate_line_count = candidate_line_count_tuple
	except Exception as e:
		print(f"Error in init_worker: {e}")
		raise

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
		
		possible_B_lines = []
		for j in range(_candidate_line_count[1]):
			allowed = True
			for i in range(10):
				if _AB_intersection[int(selected_A[i]) - 1, j] != 1: 
					allowed = False
					break
			if allowed:
				possible_B_lines.append(j)
		
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
	if self.get_satisfiability():
		return_string = ""
		timings = self.get_timings()
		count, solutions = self.get_exhaustive_solutions()
		return_string += str(solutions) + "\n"
		return_string += str(timings) + "\n"
		return_string += str(count) + "\n"
		return return_string
	else:
		return f"No solution found, and so no refinement exists for template-{template_id}."

if __name__ == "__main__":
	rewrite = False
	
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
	exhaustive_variables = candidate_line_count[0]

	current_time = time.time()

	if exhaust: # create shared memory for AB_intersection
		shm = shared_memory.SharedMemory(create=True, size=AB_intersection_np.nbytes)
		shm_array = np.ndarray(AB_intersection_np.shape, dtype=np.int8, buffer=shm.buf)
		shm_array[:] = AB_intersection_np[:]
		
		print(f"Created shared memory: {shm.name} ({AB_intersection_np.nbytes / 1024 / 1024:.2f} MB)")
		
		try:
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
			stats = {
				'processed_count': 0,
				'total_count': 0,
				'raw_A_solution_count': 0
			}
			stats_lock = threading.Lock()
			shutdown_event = threading.Event()

			def on_solution_found(solution_str):
				"""Called by run_sat_solver each time a new solution is found."""
				solution_queue.put(solution_str.split()[:10])
				with stats_lock:
					stats['raw_A_solution_count'] += 1
					if stats['raw_A_solution_count'] % 100 == 1:
						print(f"Raw A Solution Rate: (A Rate: {(stats['raw_A_solution_count']/(time.time() - current_time)):.2f}sq/s)")

			def solution_processor():
				"""Process solutions from queue and submit to pool."""
				try:
					with multiprocessing.Pool(processes=num_proc, initializer=init_worker, initargs=(shm.name, AB_intersection_np.shape, tuple(candidate_line_count))) as local_pool:
						pending_results = []
						max_pending = num_proc * 10 # limit queue depth
						
						while not shutdown_event.is_set():
							try:
								while len(pending_results) >= max_pending and not shutdown_event.is_set(): # wait for space in queue
									time.sleep(0.1)
									completed = []
									for i, async_res in enumerate(pending_results): # check for completed results
										if async_res.ready(): # is "currently being worked on A refinement" done?
											try:
												result = async_res.get() # result of A refinement
												with stats_lock:
													results_list.append(result)
													stats['processed_count'] += 1
													
													if result['status'] == 'success':
														if result['num_valid_Bs'] > 0 or stats['processed_count'] % 100 == 1:
															print(f"[{stats['processed_count']}/{stats['total_count'] if stats['total_count'] > 0 else '?'}] "
																f"A-{result['solution_id']}: {result['num_valid_Bs']} valid Bs "
																f"({result['wall_time']:.2f}s, {stats['processed_count']/(time.time() - current_time):.2f} A/s)")
													else:
														print(f"[{stats['processed_count']}/{stats['total_count'] if stats['total_count'] > 0 else '?'}] "
															  f"A-{result['solution_id']}: FAILED - {result.get('error', 'Unknown')}")
													completed.append(i)
											except Exception as e:
												print(f"Error getting result: {e}")
												completed.append(i)
									
									for i in reversed(completed):
										pending_results.pop(i) # remove all completed refinements from pending list
								
								solution = solution_queue.get(timeout=0.5) # A refinement
								if solution is None:
									break
								
								async_result = local_pool.apply_async(worker, (solution,)) # assign processor to A refinement
								pending_results.append(async_result) # add to tracking list of "currently being worked on A refinement"
								
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
								with stats_lock:
									results_list.append(result)
									stats['processed_count'] += 1
									
									if result['status'] == 'success':
										if result['num_valid_Bs'] > 0:
											print(f"[{stats['processed_count']}/{stats['total_count']}] "
												f"A-{result['solution_id']}: {result['num_valid_Bs']} valid Bs ({result['wall_time']:.2f}s)")
									else:
										print(f"[{stats['processed_count']}/{stats['total_count']}] "
											  f"A-{result['solution_id']}: FAILED")
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
					True,
					on_solution_found=on_solution_found
				)
				
				count, _ = decoding.get_exhaustive_solutions()
				with stats_lock:
					stats['total_count'] = int(count)
				print(f"\nFound {count} A configurations total. Waiting for all to be processed...")
			finally:
				solution_queue.put(None)
				processor_thread.join(timeout=600)
				if processor_thread.is_alive():
					print("WARNING: Processor thread did not finish in time")
					shutdown_event.set()
					processor_thread.join(timeout=60)

			print(f"\nCompleted processing all {stats['processed_count']} A configurations.")

			results_path = os.path.join(script_dir, f"{template_id}-all-AB-pairs.txt")
			with open(results_path, 'w') as f: # write final results
				f.write(f"Template {template_id} - Complete A-B Configuration Results\n")
				f.write(f"Total A configurations: {stats['total_count']}\n")
				f.write(f"Successfully processed: {len([r for r in results_list if r['status'] == 'success'])}\n\n")
				
				total_AB_pairs = 0
				for result in results_list:
					if result['status'] == 'success':
						total_AB_pairs += result['num_valid_Bs']
						f.write(f"A-{result['solution_id']}:\n")
						f.write(f"  Selected A indices: {result['selected_A']}\n")
						f.write(f"  Number of valid Bs: {result['num_valid_Bs']}\n")
						f.write(f"  Processing time: {result['wall_time']:.2f}s\n")
						
						if result['num_valid_Bs'] > 0 and result['num_valid_Bs'] <= 10:
							for idx, b_config in enumerate(result['valid_Bs']):
								f.write(f"    B{idx+1}: {b_config}\n")
						elif result['num_valid_Bs'] > 10:
							for idx, b_config in enumerate(result['valid_Bs'][:5]):
								f.write(f"    B{idx+1}: {b_config}\n")
							f.write(f"    ... and {result['num_valid_Bs'] - 5} more\n")
						f.write("\n")
				
				f.write(f"\nTotal valid (A, B) pairs found: {total_AB_pairs}\n")

			print(f"All results written to {results_path}")
			print(f"Total valid (A, B) pairs: {total_AB_pairs}")
		finally: # clean up shared memory
			shm.close()
			shm.unlink()
			print("Shared memory cleaned up")
	
	else: # non-exhaustive mode
		decoding = decode.SATDecoder(output_path, parseSolution)
		wall_time = decoding.run_sat_solver(satsolver_path, input_path, [], True)
		print("\n" + str(decoding))
