# Lemma 5.3: untrusted generation of the kernel checks

These programs produce the modules `DavenportCompute/Checks/*.lean`, the finite input of Lemma 5.3
that Lean's kernel checks with `decide +kernel`. Nothing here is trusted:
- the enumeration is re-run by the kernel (`DavenportCompute.Search.dfs`), and Lean proves that it
  reaches every normalized sequence (`DavenportProject.CubeFour.path_of_sorted`,
  `DavenportProject.CubeFour.leaf_of_runs`);
- every certificate is checked again by the kernel (`DavenportCompute.Search.checkEntries`), whose
  soundness is `DavenportProject.CubeFour.hasIncidenceIdentity_of_checkEntries`.

A wrong file can only make the build fail.

Codes and the normal form are those of `DavenportCompute/`:
- an element `(x₀, x₁, x₂)` of `(ZMod 4)^3` has the code `x₀ + 4x₁ + 16x₂`;
- a case is a sorted short-zero-free code list that satisfies the guards (`e₁`, `e₂`, `e₃` occur
  unless no term needs them) and the multiplicity normalization `n3cond`.

| Program | Output |
|---|---|
| `enumerate.c N MODE [out]` | counts per depth, the normalized leaves, and for `N = 18` the hard leaves |
| `classify14.c [out]` | the `N = 14` normalized leaves without a long zero set: `P` lines have a disjoint pair, `H` lines are hard |
| `orbits.c N file [tag\|-] [out]` | the canonical form of each case and the distinct orbit representatives. The canonical form is the least sorted image under the maps sending three support entries to the standard basis. |
| `certs14.c reps out` | a `±1` `𝓘_1`-certificate with five zero sets, `A + B + C = D + E` (`NONE` if there is none) |
| `certs18.c reps out` | a `±1` `𝓘_2`-certificate with eleven zero sets, built from a zero set `B` and a five-set `𝓘_1`-certificate off `B` (Lemma 2.2(2)) |
| `gen_data.py` | re-checks every representative certificate in Python and writes `data14.txt` and `data18.txt` |
| `kernel_data.c data14.txt data18.txt budget top.txt roots.txt` | replays the enumeration of `DavenportCompute.Search` and writes, in its order, a certificate for every case without a long zero set, and the split into chunks |
| `kernel_lean.py top.txt roots.txt dir` | writes the Lean modules `Top.lean`, `ChunkNNN.lean` and `Roots.lean` into `dir` |

Eight fourteen-term representatives have no five-set certificate (the `NONE` lines). Their
certificates were found by an exact integer linear solver (Hermite normal form reduction over `ℤ`).
They have 7–15 zero sets and coefficients at most 5 in absolute value, and are shipped in `hnf/`,
in the order of the `NONE` lines.

## The kernel enumeration

`kernel_data` follows `DavenportCompute.Search.dfs` exactly: the same states, the same allowed codes
(the multiplicity normalization is applied while the list grows, not only at its end), the codes in
increasing order, the test `leaf 14 1` at depth fourteen and `leaf 18 2` at depth eighteen. A test
passes at once if the code sum is a sum of at most three entries, since the complement of those
entries is then a long zero set. Otherwise it reads a certificate:
- fourteen terms with two disjoint zero sets `E`, `F`: the identity `E + F - (E ∪ F)`;
- the hard cases: the certificate of the orbit representative, moved by a linear map and a
  permutation of the positions.

The enumeration has 6,452,566 nodes. The top of the tree, down to subtrees of at most 16,000
nodes, is checked by `Checks.top`; the 7,319 subtrees below it are grouped into 512 chunks.

## Reproduction

Run these commands in this directory; the programs read and write the current directory. The
counts are those of 2026-11-13.

```sh
gcc -O3 -fopenmp -o enumerate enumerate.c
gcc -O3 -fopenmp -o classify14 classify14.c
gcc -O2 -o orbits orbits.c
gcc -O3 -fopenmp -o certs14 certs14.c
gcc -O3 -fopenmp -o certs18 certs18.c
gcc -O2 -o kernel_data kernel_data.c
./enumerate 18 3 hard18_n3.txt   # 1,267,272 leaves; 128,592 normalized; 2,352 hard
./classify14 rest14_n3.txt       # 562,180 normalized; 487,258 long; 38,461 pair; 36,461 hard
./orbits 14 rest14_n3.txt H reps14_hard.txt   # 6,963 orbits (paper: 6,963)
./orbits 18 hard18_n3.txt - reps18_hard.txt   # 64 orbits (paper: 64)
./certs14 reps14_hard.txt reps14_certs.txt    # 6,955 found; the other 8 are in hnf/
./certs18 reps18_hard.txt reps18_certs.txt    # 64 found
grep NONE reps14_certs.txt | cut -d'|' -f1 > reps14_none.txt
python3 gen_data.py                            # 6963 64 all certificates verified
./kernel_data data14.txt data18.txt 16000 top.txt roots.txt
python3 kernel_lean.py top.txt roots.txt ../../DavenportCompute/Checks
```

The last command rewrites the modules in `DavenportCompute/Checks` with identical contents.

The unnormalized counts reproduce Table 3 of the paper: 24,445,377 fourteen-term and 1,267,272
eighteen-term sequences with a fixed support basis.
