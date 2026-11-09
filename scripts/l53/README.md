# Lemma 5.3: untrusted generation of the certificate tables

These programs produce the orbit tables stored in `DavenportCompute/Data.lean`. Nothing here is
trusted:
- Lean re-checks every certificate it uses with `DavenportCompute.check`, whose soundness is
  `DavenportProject.CubeFour.hasIncidenceIdentity_of_check`.
- The enumeration that makes the tables complete is re-run in Lean (`DavenportCompute.gdfs`). Its
  completeness is proved in `DavenportProject/Bases/CubeFour/Enumeration.lean`.

A wrong table can only make the build fail.

Codes, the normal form and the enumeration are exactly those of `DavenportCompute/`:
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
| `extract_data.py` | compares those files with the tables stored in `DavenportCompute/Data.lean` |

Eight fourteen-term representatives have no five-set certificate (the `NONE` lines). Their
certificates were found by an exact integer linear solver (Hermite normal form reduction over `ℤ`).
They have 7–15 zero sets and coefficients at most 5 in absolute value, and are shipped in `hnf/`,
in the order of the `NONE` lines.

## Reproduction

Run these commands in this directory; the programs read and write the current directory. The
counts are those of 2026-11-06.

```sh
gcc -O3 -fopenmp -o enumerate enumerate.c
gcc -O3 -fopenmp -o classify14 classify14.c
gcc -O2 -o orbits orbits.c
gcc -O3 -fopenmp -o certs14 certs14.c
gcc -O3 -fopenmp -o certs18 certs18.c
./enumerate 18 3 hard18_n3.txt   # 1,267,272 leaves; 128,592 normalized; 2,352 hard
./classify14 rest14_n3.txt       # 562,180 normalized; 487,258 long; 38,461 pair; 36,461 hard
./orbits 14 rest14_n3.txt H reps14_hard.txt   # 6,963 orbits (paper: 6,963)
./orbits 18 hard18_n3.txt - reps18_hard.txt   # 64 orbits (paper: 64)
./certs14 reps14_hard.txt reps14_certs.txt    # 6,955 found; the other 8 are in hnf/
./certs18 reps18_hard.txt reps18_certs.txt    # 64 found
grep NONE reps14_certs.txt | cut -d'|' -f1 > reps14_none.txt
python3 gen_data.py                            # 6963 64 all certificates verified
python3 extract_data.py ../../DavenportCompute/Data.lean data14.txt data18.txt
```

The last command should report both tables as identical. In `Data.lean` the lines of
`data14.txt` and `data18.txt` are stored verbatim as Lean string literals, wrapped with string
gaps and split into blocks of 100 lines.

The unnormalized counts reproduce Table 3 of the paper: 24,445,377 fourteen-term and 1,267,272
eighteen-term sequences with a fixed support basis.
