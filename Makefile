CXX = g++

# Include directories
INCLUDES = -I../cadical-exhaust-master/src -I../library/nauty2_9_3 -I.

# Greatest common flags
CXXFLAGS_BASE = -std=c++20 -pipe $(INCLUDES)

# Link CaDiCaL
LDFLAGS_BASE = ../cadical-exhaust-master/build/libcadical.a
NAUTY_LIB = ../library/nauty2_9_3/nauty.a

# ===== Release build (for benchmarking) =====
CXXFLAGS_RELEASE = -O3 -march=native -DNDEBUG
LDFLAGS_RELEASE  = -flto

# Default target
all: auto dynamic

auto: automorphisms.cpp
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o automorphisms automorphisms.cpp $(NAUTY_LIB) $(LDFLAGS_BASE) $(LDFLAGS_RELEASE)

dynamic: template_dynamic.cpp automorphisms.cpp 4net_nauty.cpp partial_solution_refinement.cpp
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o template_dynamic template_dynamic.cpp $(NAUTY_LIB) $(LDFLAGS_BASE) $(LDFLAGS_RELEASE)

count: count_nonisomorphic.cpp
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o count_nonisomorphic count_nonisomorphic.cpp $(NAUTY_LIB) $(LDFLAGS_BASE) $(LDFLAGS_RELEASE) -DTHREADSAFE
 
clean:
	rm -f template_dynamic automorphisms count_nonisomorphic
	find . -name "*.gcda" -delete
	find . -name "*.gcno" -delete

.PHONY: all clean