#ifndef _proofsizetracer_hpp_INCLUDED
#define _proofsizetracer_hpp_INCLUDED

// External (outside the CaDiCaL library) tracer that measures proof size through the public tracer API. 
// It does not check anything; run it next to the built-in checker ('check=1', 'checkproof=1') if you also want the proof verified. 
//
// Besides the number of lemmas ("proof size"), it simulates the size of the binary DRAT encoding without writing a file:
//   line  = 1 marker byte ('a' / 'd' / 't' for trusted clauses) + per literal l: bytes of x = 2*|l| + (l < 0) in variable-byte encoding (7 payload bits per byte) + 1 terminating zero byte

#include "tracer.hpp"

#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

class ProofSizeTracer : public CaDiCaL::Tracer {

  static unsigned lit_bytes (int lit) {
    uint64_t x = 2 * (uint64_t) std::llabs ((long long) lit) + (lit < 0);
    unsigned res = 1;
    while (x >> 7) {
      x >>= 7;
      res++;
    }
    return res;
  }

  static int64_t line_bytes (const std::vector<int> &c) {
    int64_t res = 2; // marker + terminating zero
    for (const auto &lit : c)
      res += lit_bytes (lit);
    return res;
  }

public:
  int64_t derived_lemmas = 0;  // derived clauses added
  int64_t trusted_lemmas = 0;  // trusted ('t') clauses added
  int64_t deletions = 0;       // deletion lines
  int64_t lemma_literals = 0;  // literals in all lemmas (derived + trusted)
  int64_t delete_literals = 0; // literals in deletions
  int64_t lemma_bytes = 0;     // simulated binary DRAT bytes of all lemmas
  int64_t delete_bytes = 0;    // simulated binary DRAT bytes of deletions

  // Proof lemmas are derived clauses plus trusted clauses.  
  // Original clauses and assumption clauses arrive through other callbacks and are not counted.
  void add_derived_clause (int64_t, bool, int, const std::vector<int> &c,
                           const std::vector<int64_t> &) override {
    derived_lemmas++;
    lemma_literals += c.size ();
    lemma_bytes += line_bytes (c);
  }

  // Trusted clauses ('t' lines in DRAT-trim-t) are reported through their own callback.
  void add_trusted_clause (const std::vector<int> &c) override {
    trusted_lemmas++;
    lemma_literals += c.size ();
    lemma_bytes += line_bytes (c);
  }

  void delete_clause (int64_t, bool, const std::vector<int> &c) override {
    deletions++;
    delete_literals += c.size ();
    delete_bytes += line_bytes (c);
  }

  int64_t lemmas () const { return derived_lemmas + trusted_lemmas; }
  int64_t lines () const { return lemmas () + deletions; }
  int64_t bytes () const { return lemma_bytes + delete_bytes; }
  int64_t bits () const { return 8 * bytes (); }

  void print () const {
    printf ("c proof lemmas:            %15" PRId64 "\n", lemmas ());
    printf ("c   derived:               %15" PRId64 "\n", derived_lemmas);
    printf ("c   trusted:               %15" PRId64 "\n", trusted_lemmas);
    printf ("c proof deletions:         %15" PRId64 "\n", deletions);
    printf ("c proof lines:             %15" PRId64 "\n", lines ());
    printf ("c proof lemma literals:    %15" PRId64 "\n", lemma_literals);
    printf ("c proof deletion literals: %15" PRId64 "\n", delete_literals);
    printf ("c binary DRAT bytes:       %15" PRId64 "\n", bytes ());
    printf ("c binary DRAT bits:        %15" PRId64 "\n", bits ());
  }
};

#endif
