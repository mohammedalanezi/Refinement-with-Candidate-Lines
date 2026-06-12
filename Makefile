CXX = g++

TARGET_COMPLETE      = template_to_all_refinements
TARGET_COMPLETE_ASAN = $(TARGET_COMPLETE)_asan
SRC_COMPLETE         = $(TARGET_COMPLETE).cpp

# libexact setup
EXACTDIR = libexact-1.0
EXACT_OBJS = $(EXACTDIR)/exact.o $(EXACTDIR)/util.o
TARGET_LIBEXACT = refinement_from_partial_list_libexact
SRC_LIBEXACT = refinement_from_partial_list_libexact.cpp

# Include directories
INCLUDES = -I../cadical-exhaust-master/src -I. -I$(EXACTDIR)

# Greatest common flags
CXXFLAGS_BASE = -std=c++20 -pipe $(INCLUDES)

# Link CaDiCaL
LDFLAGS_BASE = ../cadical-exhaust-master/build/libcadical.a

# ===== Release build (for benchmarking) =====
CXXFLAGS_RELEASE = -O3 -march=native -DNDEBUG
LDFLAGS_RELEASE  = -flto

# ===== ASan build (for testing) =====
CXXFLAGS_ASAN = -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer \
                -fno-optimize-sibling-calls -fno-lto
LDFLAGS_ASAN  = -fsanitize=address,undefined -fno-lto

# Default target
all: complete

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

asan: $(SRC_COMPLETE) $(EXACT_OBJS) libexact_partial_solution_refinement.cpp
	$(CXX) $(CXXFLAGS_BASE) $(CXXFLAGS_ASAN) -o $(TARGET_COMPLETE_ASAN) $(SRC_COMPLETE) $(EXACT_OBJS) \
	$(LDFLAGS_BASE) $(LDFLAGS_ASAN)

clean:
	rm -f $(TARGET_COMPLETE) $(TARGET_COMPLETE_ASAN) $(TARGET_LIBEXACT)
	rm -f $(EXACT_OBJS)

.PHONY: all asan libexact complete clean