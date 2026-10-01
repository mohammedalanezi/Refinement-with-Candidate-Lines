#include <array>
#include <vector>
#include <utility>
#include <string>
#include <iostream>
#include <unordered_set>
#include <cstring>
#include <cstdint>
#include <cstdlib>
#include <chrono>
#include <tuple>
#include <algorithm>

#include "nauty.h"
#include "nausparse.h"

using namespace std;

// Nauty graph construction
constexpr int N_COL = 4;
constexpr int N_SYM = 4 * 10;
constexpr int N_ROW = 10 * 10;
constexpr int N_NAUTY = N_COL + N_SYM + N_ROW;

constexpr int COL0 = 0;
constexpr int COL1 = 1;
constexpr int COL2 = 2;
constexpr int COL3 = 3;
constexpr int SYM_BASE = 4;
constexpr int ROW_BASE = SYM_BASE + N_SYM;

constexpr int TOTAL_ARCS = 4 * 10 * 2 + 10 * 10 * 4 * 2;

static size_t init_v[N_NAUTY];
static int  init_d[N_NAUTY];
static int  base_e[TOTAL_ARCS];

static int init_lab[N_NAUTY];
static int init_ptn[N_NAUTY];

static void init_base_graph() {
	size_t off = 0;
	for (int t = 0; t < 4; ++t) { init_v[t] = off; init_d[t] = 10; off += 10; }
	for (int r = 0; r < 10; ++r) { int v = SYM_BASE + r;      init_v[v] = off; init_d[v] = 11; off += 11; }
	for (int c = 0; c < 10; ++c) { int v = SYM_BASE + 10 + c; init_v[v] = off; init_d[v] = 11; off += 11; }
	for (int s = 0; s < 10; ++s) { int v = SYM_BASE + 20 + s; init_v[v] = off; init_d[v] = 11; off += 11; }
	for (int s = 0; s < 10; ++s) { int v = SYM_BASE + 30 + s; init_v[v] = off; init_d[v] = 11; off += 11; }
	for (int i = 0; i < 10; ++i)
		for (int j = 0; j < 10; ++j) { int v = ROW_BASE + i * 10 + j; init_v[v] = off; init_d[v] = 4; off += 4; }
	if (off != (size_t)TOTAL_ARCS) {
		cerr << "Internal error: arc count mismatch (" << off << " vs " << TOTAL_ARCS << ")\n";
		exit(1);
	}

	for (int t = 0; t < 4; ++t)
		for (int s = 0; s < 10; ++s) base_e[init_v[t] + s] = SYM_BASE + t * 10 + s;

	for (int r = 0; r < 10; ++r) {
		int v = SYM_BASE + r;
		base_e[init_v[v] + 0] = COL0;
		for (int j = 0; j < 10; ++j) base_e[init_v[v] + 1 + j] = ROW_BASE + r * 10 + j;
	}
	for (int c = 0; c < 10; ++c) {
		int v = SYM_BASE + 10 + c;
		base_e[init_v[v] + 0] = COL1;
		for (int i = 0; i < 10; ++i) base_e[init_v[v] + 1 + i] = ROW_BASE + i * 10 + c;
	}
	for (int s = 0; s < 10; ++s) base_e[init_v[SYM_BASE + 20 + s] + 0] = COL2;
	for (int s = 0; s < 10; ++s) base_e[init_v[SYM_BASE + 30 + s] + 0] = COL3;

	for (int i = 0; i < 10; ++i)
		for (int j = 0; j < 10; ++j) {
			int v = ROW_BASE + i * 10 + j;
			base_e[init_v[v] + 0] = SYM_BASE + i;
			base_e[init_v[v] + 1] = SYM_BASE + 10 + j;
		}
}

static void init_fixed_partition() {
	for (int i = 0; i < N_NAUTY; ++i) {
		init_lab[i] = i;
		init_ptn[i] = 1;
	}
	init_ptn[3]   = 0;
	init_ptn[43]  = 0;
	init_ptn[143] = 0;
}

static inline void build_graph_sparse(const int A[10][10], const int B[10][10], int* e_work, sparsegraph& sg) {
	memcpy(e_work, base_e, sizeof(base_e));
	int cnt_a[10] = {0}, cnt_b[10] = {0};
	for (int i = 0; i < 10; ++i) {
		for (int j = 0; j < 10; ++j) {
			int cell = ROW_BASE + i * 10 + j;
			int as = A[i][j], bs = B[i][j];
			e_work[init_v[cell] + 2] = SYM_BASE + 20 + as;
			e_work[init_v[cell] + 3] = SYM_BASE + 30 + bs;
			e_work[init_v[SYM_BASE + 20 + as] + 1 + (cnt_a[as]++)] = cell;
			e_work[init_v[SYM_BASE + 30 + bs] + 1 + (cnt_b[bs]++)] = cell;
		}
	}
	sg.nv = N_NAUTY;
	sg.nde = TOTAL_ARCS;
	sg.v = init_v;
	sg.d = init_d;
	sg.e = e_work;
	sg.vlen = N_NAUTY;
	sg.dlen = N_NAUTY;
	sg.elen = TOTAL_ARCS;
	sg.w = nullptr;
	sg.wlen = 0;
}

// Certificate packing
constexpr int TRI_BITS  = N_NAUTY * (N_NAUTY - 1) / 2;
constexpr int TRI_WORDS = (TRI_BITS + 63) / 64;

struct CertKey {
	uint64_t w[TRI_WORDS];
	bool operator==(const CertKey& o) const { return memcmp(w, o.w, sizeof(w)) == 0; }
};
struct CertKeyHash {
	size_t operator()(const CertKey& k) const {
		const uint8_t* p = reinterpret_cast<const uint8_t*>(k.w);
		size_t h = 1469598103934665603ULL;
		for (size_t i = 0; i < sizeof(k.w); ++i) { h ^= p[i]; h *= 1099511628211ULL; }
		return h;
	}
};
using CertSet = unordered_set<CertKey, CertKeyHash>;

static inline CertKey pack_certificate(const sparsegraph& canon_sg) {
	CertKey key;
	memset(key.w, 0, sizeof(key.w));
	static uint8_t present[N_NAUTY][N_NAUTY];
	memset(present, 0, sizeof(present));
	for (int v = 0; v < canon_sg.nv; ++v) {
		size_t base = canon_sg.v[v];
		int deg = canon_sg.d[v];
		for (int k = 0; k < deg; ++k) {
			int u = canon_sg.e[base + k];
			present[v][u] = 1;
			present[u][v] = 1;
		}
	}
	size_t bitpos = 0;
	for (int i = 0; i < N_NAUTY; ++i)
		for (int j = i + 1; j < N_NAUTY; ++j) {
			if (present[i][j]) key.w[bitpos >> 6] |= (uint64_t(1) << (bitpos & 63));
			++bitpos;
		}
	return key;
}

// WorkerState
struct WorkerState {
	int e_work[TOTAL_ARCS];
	sparsegraph sg;
	sparsegraph canon_sg;
	DEFAULTOPTIONS_SPARSEGRAPH(options);
	statsblk stats;
	CertSet certs;
	long long pairs_seen = 0;

	WorkerState() {
		SG_INIT(sg);
		SG_INIT(canon_sg);
		options.getcanon     = TRUE;
		options.writeautoms  = FALSE;
		options.writemarkers = FALSE;
		options.defaultptn   = FALSE;
	}

	inline void process_pair(const int A[10][10], const int B[10][10]) {
		++pairs_seen;
		build_graph_sparse(A, B, e_work, sg);

		int lab[N_NAUTY], ptn[N_NAUTY], orbits[N_NAUTY];
		memcpy(lab, init_lab, sizeof(lab));
		memcpy(ptn, init_ptn, sizeof(ptn));
		sparsenauty(&sg, lab, ptn, orbits, &options, &stats, &canon_sg);

		CertKey key = pack_certificate(canon_sg);
		certs.insert(key);
	}
};
