// Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
// SPDX-License-Identifier: Apache-2.0
// Certificate data for the kernel-checked enumeration of Lemma 5.3 (DavenportCompute/Search.lean).
//
// Replays `DavenportCompute.Search.dfs` exactly: the same states, the same candidate codes, the
// children in increasing order, the test `leaf 14 1` at depth 14 and `leaf 18 2` at depth 18. At
// every test whose sequence has no long zero set it writes a certificate, in the order in which the
// Lean enumeration reads them:
//   - 14 terms with two disjoint zero sets E, F: the identity E + F - (E u F);
//   - otherwise (the hard cases): the certificate of the stored orbit representative (data14.txt,
//     data18.txt), moved to the sequence by a linear map and a permutation of the positions.
// Every certificate is checked here as well, but nothing here is trusted: Lean checks them again.
//
// Output: top.txt lists, for the nodes visited by `topDfs` in order, 0 (descend) or the token of a
// chunk root; roots.txt has one line per chunk root, in order:
//   <token> <nodes in its subtree> <certificates> | <20-bit words ...>
// A certificate is its number of entries followed by the entries 2E (coefficient 1) or 2E + 1
// (coefficient -1); a coefficient c with |c| > 1 is written as |c| entries.
//
// Usage: kernel_data data14.txt data18.txt <node budget per chunk root> top.txt roots.txt
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint64_t u64;
static int ADD[64][64], NEG[64];
static int dig(int x, int i) { return (x >> (2 * i)) & 3; }
static int P1(int x) { return (dig(x, 0) | dig(x, 1) | dig(x, 2)) & 1; }
static int P2(int x) { return (dig(x, 1) | dig(x, 2)) & 1; }
static int P3(int x) { return dig(x, 2) & 1; }
static u64 G1, G4, G16;

static u64 transl(u64 S, int y) {
  u64 T = 0;
  for (int a = 0; a < 64; a++) if (S >> a & 1) T |= 1ULL << ADD[a][y];
  return T;
}
static u64 gmask(int c1, int c4, int c16) {
  return (c1 ? 0 : G1) | (c4 ? 0 : G4) | (c16 ? 0 : G16);
}

typedef struct { int lo; u64 N1, N2, F, G; int c1, c4, c16, run, s, n; int codes[18]; } State;

static State root(void) {
  State st; memset(&st, 0, sizeof st); st.lo = 1; st.G = gmask(0, 0, 0); return st;
}
static State step(const State *st, int x) {
  State r = *st; int nx = NEG[x];
  u64 T1 = transl(st->N1, nx), T2 = transl(st->N2, nx);
  r.N1 = st->N1 | 1ULL << nx; r.N2 = st->N2 | T1; r.F = st->F | 1ULL << nx | T1 | T2;
  if (x == 1) r.c1++;
  if (x == 4) r.c4++;
  if (x == 16) r.c16++;
  r.G = gmask(r.c1, r.c4, r.c16);
  r.run = (x == st->lo) ? st->run + 1 : 1;
  r.lo = x; r.s = ADD[st->s][x]; r.codes[r.n++] = x;
  return r;
}
static int okRep(const State *st) {
  int m = st->run + 1, x = st->lo;
  return (!P1(x) || x == 1 || m <= st->c1) && (!P2(x) || x == 4 || m <= st->c4) &&
         (!P3(x) || x == 16 || m <= st->c16);
}
static u64 cands(const State *st) {
  u64 base = ~(st->F | st->G | ((1ULL << st->lo) - 1));
  if ((base >> st->lo & 1) && !okRep(st)) base ^= 1ULL << st->lo;
  return base;
}
static int isLong(const State *st) { return (int)((st->F | 1) >> NEG[st->s] & 1); }

// ---------- certificates ----------
typedef struct { int mask, coef; } Ent;

static int checkCert(int t, const int *c, int n, const Ent *e, int k) {
  for (int i = 0; i < k; i++) {
    if (e[i].mask == 0 || (e[i].mask >> n)) return 0;
    int s = 0;
    for (int j = 0; j < n; j++) if (e[i].mask >> j & 1) s = ADD[s][c[j]];
    if (s) return 0;
  }
  int tot = 0; for (int i = 0; i < k; i++) tot += e[i].coef;
  if (tot != 1) return 0;
  for (int j = 0; j < n; j++) {
    int v = 0; for (int i = 0; i < k; i++) if (e[i].mask >> j & 1) v += e[i].coef;
    if (v) return 0;
  }
  if (t >= 2)
    for (int j = 0; j < n; j++) for (int l = j + 1; l < n; l++) {
      int v = 0, J = (1 << j) | (1 << l);
      for (int i = 0; i < k; i++) if ((e[i].mask & J) == J) v += e[i].coef;
      if (v) return 0;
    }
  return 1;
}

// orbit tables: sorted code lists with certificates
#define HSIZE (1 << 16)
typedef struct { int used, n; int codes[18]; int k; Ent ent[40]; } Rep;
static Rep *H14, *H18;
static unsigned hashc(const int *c, int n) {
  unsigned h = 2166136261u;
  for (int i = 0; i < n; i++) { h ^= (unsigned)c[i]; h *= 16777619u; }
  return h;
}
static Rep *lookup(Rep *H, const int *c, int n, int insert) {
  unsigned h = hashc(c, n) & (HSIZE - 1);
  while (H[h].used) {
    if (H[h].n == n && !memcmp(H[h].codes, c, sizeof(int) * n)) return &H[h];
    h = (h + 1) & (HSIZE - 1);
  }
  if (!insert) return NULL;
  H[h].used = 1; H[h].n = n; memcpy(H[h].codes, c, sizeof(int) * n);
  return &H[h];
}
static void loadTable(Rep *H, const char *path, int n, int t) {
  FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
  char line[4096]; int cnt = 0;
  while (fgets(line, sizeof line, f)) {
    char *p = line; int c[18];
    for (int i = 0; i < n; i++) c[i] = (int)strtol(p, &p, 10);
    p = strchr(p, '|'); if (!p) continue; p++;
    Rep *r = lookup(H, c, n, 1); r->k = 0;
    long m, k;
    while (sscanf(p, "%ld %ld", &m, &k) == 2) {
      r->ent[r->k].mask = (int)m; r->ent[r->k].coef = (int)k; r->k++;
      for (int s = 0; s < 2; s++) { while (*p == ' ') p++; while (*p && *p != ' ' && *p != '\n') p++; }
    }
    if (!checkCert(t, c, n, r->ent, r->k)) { fprintf(stderr, "bad table certificate\n"); exit(1); }
    cnt++;
  }
  fclose(f); fprintf(stderr, "%s: %d representatives\n", path, cnt);
}

// linear maps sending three support entries to the standard basis (as in orbits.c)
static int det3(int r0, int r1, int r2) {
  int m[3][3], rs[3] = {r0, r1, r2};
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) m[i][j] = dig(rs[i], j);
  int d = m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1]) - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0]) +
          m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]);
  return ((d % 4) + 4) % 4;
}
static void inv3(int r0, int r1, int r2, int inv[3][3]) {
  int m[3][3], rs[3] = {r0, r1, r2};
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) m[i][j] = dig(rs[i], j);
  int di = det3(r0, r1, r2) == 1 ? 1 : 3, adj[3][3];
  adj[0][0] = m[1][1] * m[2][2] - m[1][2] * m[2][1]; adj[0][1] = -(m[0][1] * m[2][2] - m[0][2] * m[2][1]);
  adj[0][2] = m[0][1] * m[1][2] - m[0][2] * m[1][1]; adj[1][0] = -(m[1][0] * m[2][2] - m[1][2] * m[2][0]);
  adj[1][1] = m[0][0] * m[2][2] - m[0][2] * m[2][0]; adj[1][2] = -(m[0][0] * m[1][2] - m[0][2] * m[1][0]);
  adj[2][0] = m[1][0] * m[2][1] - m[1][1] * m[2][0]; adj[2][1] = -(m[0][0] * m[2][1] - m[0][1] * m[2][0]);
  adj[2][2] = m[0][0] * m[1][1] - m[0][1] * m[1][0];
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) inv[i][j] = (((adj[i][j] * di) % 4) + 4) % 4;
}
static int apply(int v, int inv[3][3]) {
  int r = 0;
  for (int j = 0; j < 3; j++) { int s = 0; for (int i = 0; i < 3; i++) s += dig(v, i) * inv[i][j]; r |= (s & 3) << (2 * j); }
  return r;
}
// a certificate for c moved from a stored representative; returns the number of entries
static int transport(Rep *H, const int *c, int n, int t, Ent *out) {
  int sup[18], ns = 0;
  for (int i = 0; i < n; i++) { int seen = 0; for (int j = 0; j < ns; j++) if (sup[j] == c[i]) seen = 1; if (!seen) sup[ns++] = c[i]; }
  for (int a = 0; a < ns; a++) for (int b = 0; b < ns; b++) for (int d = 0; d < ns; d++) {
    if (a == b || a == d || b == d || !(det3(sup[a], sup[b], sup[d]) & 1)) continue;
    int inv[3][3]; inv3(sup[a], sup[b], sup[d], inv);
    int img[18], idx[18];
    for (int i = 0; i < n; i++) { img[i] = apply(c[i], inv); idx[i] = i; }
    for (int i = 1; i < n; i++) for (int j = i; j > 0 && img[idx[j - 1]] > img[idx[j]]; j--) { int tmp = idx[j]; idx[j] = idx[j - 1]; idx[j - 1] = tmp; }
    int key[18]; for (int i = 0; i < n; i++) key[i] = img[idx[i]];
    Rep *r = lookup(H, key, n, 0);
    if (!r) continue;
    for (int i = 0; i < r->k; i++) {
      int m = 0; for (int j = 0; j < n; j++) if (r->ent[i].mask >> j & 1) m |= 1 << idx[j];
      out[i].mask = m; out[i].coef = r->ent[i].coef;
    }
    if (!checkCert(t, c, n, out, r->k)) { fprintf(stderr, "transported certificate fails\n"); exit(1); }
    return r->k;
  }
  return -1;
}
static int disjointPair(const int *c, int n, Ent *out) {
  static int sum[1 << 14], Z[1 << 14];
  int nz = 0; sum[0] = 0;
  for (int m = 1; m < (1 << n); m++) { sum[m] = ADD[sum[m & (m - 1)]][c[__builtin_ctz(m)]]; if (!sum[m]) Z[nz++] = m; }
  for (int i = 0; i < nz; i++) for (int j = i + 1; j < nz; j++) if (!(Z[i] & Z[j])) {
    out[0].mask = Z[i]; out[0].coef = 1; out[1].mask = Z[j]; out[1].coef = 1;
    out[2].mask = Z[i] | Z[j]; out[2].coef = -1;
    return 3;
  }
  return -1;
}

// ---------- output buffer of 20-bit words for the current prefix ----------
static int *W; static long nW, capW;
static void word(int w) {
  if (w < 0 || w >= (1 << 20)) { fprintf(stderr, "word out of range\n"); exit(1); }
  if (nW == capW) { capW = capW ? 2 * capW : 1024; W = realloc(W, sizeof(int) * capW); }
  W[nW++] = w;
}
static void emit(const Ent *e, int k) {
  int cnt = 0; for (int i = 0; i < k; i++) cnt += abs(e[i].coef);
  word(cnt);
  for (int i = 0; i < k; i++) for (int r = 0; r < abs(e[i].coef); r++) word(2 * e[i].mask + (e[i].coef < 0));
}

static long nodes, nCert, stat[8];
static void leafTest(const State *st, int n, int t) {
  if (isLong(st)) { stat[n == 14 ? 0 : 3]++; return; }
  Ent e[64]; int k = -1;
  if (n == 14) { k = disjointPair(st->codes, n, e); if (k > 0) stat[1]++; }
  if (k < 0) { k = transport(n == 14 ? H14 : H18, st->codes, n, t, e); stat[n == 14 ? 2 : 4]++; }
  if (k < 0) { fprintf(stderr, "no certificate\n"); exit(1); }
  if (!checkCert(t, st->codes, n, e, k)) { fprintf(stderr, "bad certificate\n"); exit(1); }
  emit(e, k); nCert++;
}
// the subtree of `st` with `rem` codes still to append (as `dfs (leaf 14 1) (leaf 18 2) 3`)
static void dfs(const State *st, int rem) {
  nodes++;
  if (rem == 0) { leafTest(st, 18, 2); return; }
  if (rem == 4) leafTest(st, 14, 1);
  u64 c = cands(st);
  while (c) { int x = __builtin_ctzll(c); c &= c - 1; State ch = step(st, x); dfs(&ch, rem - 1); }
}

// ---------- splitting into chunks ----------
// A node is named by its token 16 * q + depth (q: its packed codes). Pass 1 marks the nodes of depth
// below 14 whose subtree has more than BUDGET nodes; pass 2 descends exactly into the marked nodes,
// and the other nodes it reaches are the chunk roots.
typedef unsigned __int128 u128;
static long BUDGET;
static u128 token(const State *st) { u128 q = 0; for (int i = 0; i < st->n; i++) q = (q << 6) | st->codes[i]; return q * 16 + st->n; }
#define MSIZE (1 << 20)
static u128 *Marked; static char *MarkedUsed;
static void mark(u128 t) { unsigned h = (unsigned)(t ^ (t >> 64)) * 2654435761u & (MSIZE - 1); while (MarkedUsed[h]) h = (h + 1) & (MSIZE - 1); MarkedUsed[h] = 1; Marked[h] = t; }
static int marked(u128 t) { unsigned h = (unsigned)(t ^ (t >> 64)) * 2654435761u & (MSIZE - 1); while (MarkedUsed[h]) { if (Marked[h] == t) return 1; h = (h + 1) & (MSIZE - 1); } return 0; }
static long sizeOf(const State *st, int rem) {
  long n = 1;
  if (rem > 0) { u64 c = cands(st); while (c) { int x = __builtin_ctzll(c); c &= c - 1; State ch = step(st, x); n += sizeOf(&ch, rem - 1); } }
  if (st->n < 14 && n > BUDGET) mark(token(st));
  return n;
}
static void print128(FILE *f, u128 v) { char buf[64]; int i = 63; buf[i] = 0; if (!v) buf[--i] = '0'; while (v) { buf[--i] = '0' + (int)(v % 10); v /= 10; } fputs(buf + i, f); }
static FILE *TOP, *OUT;
static long nRoots, nDesc;
static void top(const State *st) {
  if (marked(token(st))) {
    if (st->n >= 14) { fprintf(stderr, "cannot descend at depth 14\n"); exit(1); }
    fprintf(TOP, "0\n"); nDesc++;
    u64 c = cands(st);
    while (c) { int x = __builtin_ctzll(c); c &= c - 1; State ch = step(st, x); top(&ch); }
    return;
  }
  print128(TOP, token(st)); fprintf(TOP, "\n"); nRoots++;
  nodes = 0; nCert = 0; nW = 0;
  dfs(st, 18 - st->n);
  print128(OUT, token(st)); fprintf(OUT, " %ld %ld |", nodes, nCert);
  for (long i = 0; i < nW; i++) fprintf(OUT, " %d", W[i]);
  fprintf(OUT, "\n");
}

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: kernel_data data14.txt data18.txt budget top.txt roots.txt\n"); return 1; }
  for (int a = 0; a < 64; a++) for (int b = 0; b < 64; b++) {
    int r = 0; for (int i = 0; i < 3; i++) r |= ((dig(a, i) + dig(b, i)) & 3) << (2 * i);
    ADD[a][b] = r;
  }
  for (int a = 0; a < 64; a++) for (int b = 0; b < 64; b++) if (!ADD[a][b]) NEG[a] = b;
  for (int x = 0; x < 64; x++) {
    if (P1(x) && x != 1) G1 |= 1ULL << x;
    if (P2(x) && x != 4) G4 |= 1ULL << x;
    if (P3(x) && x != 16) G16 |= 1ULL << x;
  }
  H14 = calloc(HSIZE, sizeof(Rep)); H18 = calloc(HSIZE, sizeof(Rep));
  loadTable(H14, argv[1], 14, 1); loadTable(H18, argv[2], 18, 2);
  BUDGET = atol(argv[3]);
  Marked = calloc(MSIZE, sizeof(u128)); MarkedUsed = calloc(MSIZE, 1);
  TOP = fopen(argv[4], "w"); OUT = fopen(argv[5], "w"); if (!TOP || !OUT) { perror("output"); return 1; }
  State r = root();
  long total = sizeOf(&r, 18);
  top(&r);
  fclose(TOP); fclose(OUT);
  fprintf(stderr, "%ld nodes; %ld descended, %ld chunk roots\n", total, nDesc, nRoots);
  fprintf(stderr, "14 terms: %ld long, %ld disjoint pairs, %ld moved | 18 terms: %ld long, %ld moved\n",
          stat[0], stat[1], stat[2], stat[3], stat[4]);
  return 0;
}
