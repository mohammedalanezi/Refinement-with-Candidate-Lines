CXX = g++

TARGET = refinement_from_partial_list
TARGET_ASAN = $(TARGET)_asan
TARGET_MULTI = $(TARGET)_mt
TARGET_ASSUME = $(TARGET)_assumption
SRC = $(TARGET).cpp
SRC_ASSUME = $(TARGET)_assumption.cpp

# Include directories
INCLUDES = -I../cadical-exhaust-master/src -I. -I$(EXACTDIR)

# Greatest common flags
CXXFLAGS_BASE = -std=c++20 -pipe $(INCLUDES)
MULTI_THREAD  = -pthread -fopenmp

# Link CaDiCaL
LDFLAGS_BASE = ../cadical-exhaust-master/build/libcadical.a

# ===== Release build (for benchmarking) =====
CXXFLAGS_RELEASE = -O3 -DNDEBUG
LDFLAGS_RELEASE  =

# ===== ASan build (for testing) =====
CXXFLAGS_ASAN = -O1 -g -fsanitize=address -fno-omit-frame-pointer -fno-lto
LDFLAGS_ASAN  = -fsanitize=address

# Default target
all: single

single:
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o $(TARGET) $(SRC) \
	$(LDFLAGS_BASE) $(LDFLAGS_RELEASE)

multi:
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o $(TARGET_MULTI) $(SRC) \
	$(MULTI_THREAD) $(LDFLAGS_BASE) $(LDFLAGS_RELEASE)

assume:
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o $(TARGET_ASSUME) $(SRC_ASSUME) \
	$(LDFLAGS_BASE) $(LDFLAGS_RELEASE)

asan:
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_ASAN) -o $(TARGET_ASAN) $(SRC) \
	$(LDFLAGS_BASE) $(LDFLAGS_ASAN)

clean:
	rm -f $(TARGET) $(TARGET_ASAN) $(TARGET_MULTI)

.PHONY: all single multi asan clean