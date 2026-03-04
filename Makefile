CXX = g++

TARGET = refinement_from_partial_list
TARGET_ASAN = $(TARGET)_asan
SRC = refinement_from_partial_list.cpp

# Include directories
INCLUDES = -I../cadical-exhaust-master/src -I. -I$(EXACTDIR)

# Base flags (common to both builds)
CXXFLAGS_BASE = -std=c++20 -pipe -pthread $(INCLUDES)
LDFLAGS_BASE  = -pthread -fopenmp

# Link CaDiCaL
LDFLAGS_BASE += ../cadical-exhaust-master/build/libcadical.a

# ===== Release build (for benchmarking) =====
CXXFLAGS_RELEASE = -O3 -march=native -DNDEBUG
LDFLAGS_RELEASE  =

# ===== ASan build (for testing) =====
CXXFLAGS_ASAN = -O1 -g -fsanitize=address -fno-omit-frame-pointer -fno-lto
LDFLAGS_ASAN  = -fsanitize=address

# Default target
all: release

release:
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o $(TARGET) $(SRC) \
	$(LDFLAGS_BASE) $(LDFLAGS_RELEASE)

asan:
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_ASAN) -o $(TARGET_ASAN) $(SRC) \
	$(LDFLAGS_BASE) $(LDFLAGS_ASAN)

clean:
	rm -f $(TARGET) $(TARGET_ASAN)

.PHONY: all release asan clean