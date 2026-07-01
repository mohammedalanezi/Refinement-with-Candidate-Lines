CXX = g++

TARGET_COMPLETE      = template_to_all_refinements
TARGET_COMPLETE_ASAN = $(TARGET_COMPLETE)_asan
SRC_COMPLETE         = $(TARGET_COMPLETE).cpp

TARGET_TEMPLATE      = search_templates
SRC_TEMPLATE         = $(TARGET_TEMPLATE).cpp

# Include directories
INCLUDES = -I../cadical-exhaust-master/src -I./nauty2_9_3 -I. 

# Greatest common flags
CXXFLAGS_BASE = -std=c++20 -pipe $(INCLUDES)

# Link CaDiCaL
LDFLAGS_BASE = ../cadical-exhaust-master/build/libcadical.a
NAUTY_LIB = ./nauty2_9_3/nauty.a

# ===== Release build (for benchmarking) =====
CXXFLAGS_RELEASE = -O3 -march=native -DNDEBUG 
LDFLAGS_RELEASE  = -flto

# ===== ASan build (for testing) =====
CXXFLAGS_ASAN = -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer -fno-optimize-sibling-calls -fno-lto
LDFLAGS_ASAN  = -fsanitize=address,undefined -fno-lto

# Default target
all: complete asan template

complete: $(SRC_COMPLETE) partial_solution_refinement.cpp
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o $(TARGET_COMPLETE) $(SRC_COMPLETE) $(LDFLAGS_BASE) $(LDFLAGS_RELEASE)

asan: $(SRC_COMPLETE) $(EXACT_OBJS) partial_solution_refinement.cpp
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_ASAN) -o $(TARGET_COMPLETE_ASAN) $(SRC_COMPLETE) $(LDFLAGS_BASE) $(LDFLAGS_ASAN)
    
template: $(SRC_TEMPLATE)
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o $(TARGET_TEMPLATE) $(SRC_TEMPLATE) $(NAUTY_LIB) $(LDFLAGS_BASE) $(LDFLAGS_RELEASE)

clean:
	rm -f $(TARGET_COMPLETE) $(TARGET_COMPLETE_ASAN) $(TARGET_LIBEXACT) $(TARGET_TEMPLATE) 
	find . -name "*.gcda" -delete
	find . -name "*.gcno" -delete

.PHONY: all asan libexact complete template clean