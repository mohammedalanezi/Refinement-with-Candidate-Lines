CXX = g++

TARGET = refinement_from_partial_list
TARGET_ASAN = $(TARGET)_asan
TARGET_MULTI = $(TARGET)_mt
#TARGET_ASSUME = $(TARGET)_assumption
SRC = $(TARGET).cpp
#SRC_ASSUME = $(TARGET)_assumption.cpp

#TARGET_ACC = all_candidate_encoding
#SRC_ACC    = all_candidate_encoding.cpp

TARGET_COMPLETE = template_to_all_refinements
SRC_COMPLETE = $(TARGET_COMPLETE).cpp

# libexact setup
EXACTDIR = libexact-1.0
EXACT_OBJS = $(EXACTDIR)/exact.o $(EXACTDIR)/util.o
TARGET_LIBEXACT = refinement_from_partial_list_libexact
SRC_LIBEXACT = refinement_from_partial_list_libexact.cpp

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

#assume:
#	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o $(TARGET_ASSUME) exhaustive_alt.hpp $(SRC_ASSUME) \
#	$(LDFLAGS_BASE) $(LDFLAGS_RELEASE)

asan:
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_ASAN) -o $(TARGET_ASAN) $(SRC) \
	$(LDFLAGS_BASE) $(LDFLAGS_ASAN)

#test:
#	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o test_assumption exhaustive_alt.hpp emptypropagator.hpp test_assumption.cpp \
#	$(LDFLAGS_BASE) $(LDFLAGS_RELEASE)

#acc:
#	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o $(TARGET_ACC) $(SRC_ACC) \
#	$(LDFLAGS_BASE) $(LDFLAGS_RELEASE)

# Compile libexact object files
$(EXACTDIR)/exact.o: $(EXACTDIR)/exact.c $(EXACTDIR)/exact.h $(EXACTDIR)/util.h
	$(CC) $(CFLAGS) -I$(EXACTDIR) -c -o $@ $(EXACTDIR)/exact.c

$(EXACTDIR)/util.o: $(EXACTDIR)/util.c $(EXACTDIR)/util.h
	$(CC) $(CFLAGS) -I$(EXACTDIR) -c -o $@ $(EXACTDIR)/util.c

# Build the libexact-based executables
libexact: $(SRC_LIBEXACT) $(EXACT_OBJS)
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o $(TARGET_LIBEXACT) $(SRC_LIBEXACT) $(EXACT_OBJS) $(LDFLAGS_BASE) $(LDFLAGS_RELEASE)

complete: $(SRC_COMPLETE) $(EXACT_OBJS) libexact_partial_solution_refinement.cpp
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_RELEASE) -o $(TARGET_COMPLETE) $(SRC_COMPLETE) $(EXACT_OBJS) $(LDFLAGS_BASE) $(LDFLAGS_RELEASE)

clean:
	rm -f $(TARGET) $(TARGET_ASAN) $(TARGET_MULTI) $(TARGET_LIBEXACT) $(TARGET_COMPLETE)
	rm -f $(EXACT_OBJS)

.PHONY: all single multi asan libexact complete clean