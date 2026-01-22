"""
Statistics Classes 
Used for global numerical counters and event rate trackers. 
An event-based system, focusing on per second changes over rolling windows.

By Mohammed Al-Anezi.
"""

# Track total counters
# Track process rates/changes in the counters
#	Top, Average, and Bottom 60s timeframes

import time
from collections import deque
import threading

class RateTracker:
	"""Track rates over a rolling 60-second window."""
	def __init__(self, window_seconds=60):
		self.window_seconds = window_seconds
		self.timestamps = deque()
		self.lock = threading.Lock()
	
	def add_event(self):
		"""Record a new event."""
		with self.lock:
			current_time = time.time()
			self.timestamps.append(current_time)
			self._clean_old_events(current_time)
	
	def _clean_old_events(self, current_time):
		"""Remove events older than window_seconds."""
		cutoff_time = current_time - self.window_seconds
		while self.timestamps and self.timestamps[0] < cutoff_time:
			self.timestamps.popleft()
	
	def get_rate(self):
		"""Get current rate (events per second) over the window."""
		with self.lock:
			current_time = time.time()
			self._clean_old_events(current_time)
			if len(self.timestamps) == 0:
				return 0.0
			return len(self.timestamps) / self.window_seconds

class PerformanceStats:
	"""Track comprehensive performance statistics."""
	def __init__(self):
		self.lock = threading.Lock()
		# counters
		self.raw_A_count = 0 # total A configurations found by SAT solver 1
		self.processed_A_count = 0 # total processed A configurations by SAT solver 2
		self.total_B_count = 0 # total B configurations found across all A's using Sat solver 2
		
		# rate trackers (60s rolling windows)
		self.raw_A_tracker = RateTracker(60)
		self.processed_A_tracker = RateTracker(60)
		self.B_tracker = RateTracker(60)
		
		# statistics for rates over time
		self.raw_A_rates = [] # total rates for raw A
		self.processed_A_rates = [] # total rates for processed A
		self.B_rates = [] # total rates for B
		
		self.start_time = time.time()
		self.last_stats_time = time.time()
	
	def record_raw_A(self):
		"""Record finding a new raw A configuration."""
		with self.lock:
			self.raw_A_count += 1
			self.raw_A_tracker.add_event()
	
	def record_processed_A(self, num_Bs):
		"""Record completion of processing an A configuration."""
		with self.lock:
			self.processed_A_count += 1
			self.total_B_count += num_Bs
			self.processed_A_tracker.add_event()
			for _ in range(num_Bs): # include each B individually as an event
				self.B_tracker.add_event()
	
	def get_current_rates(self):
		"""Get current rates for all metrics."""
		return {
			'raw_A_rate': self.raw_A_tracker.get_rate(),
			'processed_A_rate': self.processed_A_tracker.get_rate(),
			'B_rate': self.B_tracker.get_rate()
		}
	
	def snapshot_rates(self):
		"""Take a snapshot of current rates for historical tracking."""
		with self.lock:
			current_time = time.time()
			if current_time - self.last_stats_time >= 6.0: # snapshot every 6 seconds to avoid too much data
				rates = self.get_current_rates()
				self.raw_A_rates.append(rates['raw_A_rate'])
				self.processed_A_rates.append(rates['processed_A_rate'])
				self.B_rates.append(rates['B_rate'])
				self.last_stats_time = current_time
	
	def get_rate_statistics(self, rate_list):
		"""Calculate top, avg, bottom rates from a list."""
		if not rate_list:
			return {'top': 0.0, 'avg': 0.0, 'bottom': 0.0}
		
		non_zero_rates = [r for r in rate_list if r > 0.0] # filter out zero rates 
		if not non_zero_rates:
			return {'top': 0.0, 'avg': 0.0, 'bottom': 0.0}
		
		return {
			'top': max(non_zero_rates),
			'avg': sum(non_zero_rates) / len(non_zero_rates),
			'bottom': min(non_zero_rates)
		}
	
	def get_rate_raw_statistics(self, rate_list):
		"""Calculate top, avg, bottom rates from a list."""
		if not rate_list:
			return {'top': 0.0, 'avg': 0.0, 'bottom': 0.0}
		
		return {
			'top': max(rate_list),
			'avg': sum(rate_list) / len(rate_list),
			'bottom': min(rate_list)
		}
	
	def get_summary(self):
		"""Get complete performance summary."""
		with self.lock:
			elapsed = time.time() - self.start_time
			current_rates = self.get_current_rates()
			
			return {
				'elapsed_time': elapsed,
				'counts': {
					'raw_A': self.raw_A_count,
					'processed_A': self.processed_A_count,
					'total_B': self.total_B_count
				},
				'current_rates': current_rates,
				'overall_rates': {
					'raw_A': self.raw_A_count / elapsed if elapsed > 0 else 0,
					'processed_A': self.processed_A_count / elapsed if elapsed > 0 else 0,
					'B': self.total_B_count / elapsed if elapsed > 0 else 0
				},
				'rate_stats_60s': {
					'raw_A': self.get_rate_statistics(self.raw_A_rates),
					'processed_A': self.get_rate_statistics(self.processed_A_rates),
					'B': self.get_rate_statistics(self.B_rates)
				},
				'raw_rate_stats_60s': {
					'raw_A': self.get_rate_raw_statistics(self.raw_A_rates),
					'processed_A': self.get_rate_raw_statistics(self.processed_A_rates),
					'B': self.get_rate_raw_statistics(self.B_rates)
				}
			}