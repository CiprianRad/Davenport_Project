# Davenport_Project

[![CI](https://github.com/CiprianRad/Davenport_Project/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/CiprianRad/Davenport_Project/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of the paper *Integral zero-sum incidence identities and Davenport constants
in rank three* by C. G. Pop, G. C. Rad and G. C. Țurcaș. The statement numbers below are those of
the manuscript of November 2026 (version 4), with which every formal statement has been compared;
see [Relation to the paper](#relation-to-the-paper).

## Results

| Paper | Lean declaration (namespace `DavenportProject`) | File |
|---|---|---|
| Zero sets | `IsZeroSet`, `zeroSets` | `DavenportProject/Defs.lean` |
| Incidence identities, eq. (1.3) | `IsIncidenceIdentity`, `HasIncidenceIdentity` | `DavenportProject/Defs.lean` |
| Separators | `IsSeparator`, `HasSeparator` | `DavenportProject/Defs.lean` |
| Short-zero-free sequences | `IsShortZeroFree` | `DavenportProject/Defs.lean` |
| The Davenport constant `D(G)` | `davenport`, `davenport_eq_iff` | `DavenportProject/Invariants.lean` |
| The invariant `κ_t(G; K)` | `kappa`, `kappa_eq_iff` | `DavenportProject/Invariants.lean` |
| Lemma 2.1(1), (2) | `isIncidenceIdentity_iff_eval`, `IsIncidenceIdentity.intCast` | `DavenportProject/Identities/Evaluation.lean` |
| Lemma 2.1(3) | `hasIncidenceIdentity_iff_not_hasSeparator` | `DavenportProject/Identities/Duality.lean` |
| Lemma 2.2(1), (2), (3) | `hasIncidenceIdentity_of_pairwise_disjoint`, `hasIncidenceIdentity_of_disjoint_zeroSet`, `hasIncidenceIdentity_of_ssubset_zeroSet` | `DavenportProject/Identities/Operations.lean` |
| Lemma 3.1 | `exists_multilinear_zeroSum_indicator` | `DavenportProject/Transfer/Indicator.lean` |
| Olson's theorem (cited in the paper) | `davenport_pi_zmod_prime_pow` | `DavenportProject/Transfer/Olson.lean` |
| Theorem A | `davenport_prod_le_of_hasIncidenceIdentity_zmod`, `davenport_prod_le_of_hasIncidenceIdentity_int` | `DavenportProject/Transfer/TheoremA.lean` |
| Remark 3.2: `η`, short blocks and the classical product bound | `eta`, `eta_eq_iff`, `Transfer.exists_disjoint_shortZeroSets`, `hasIncidenceIdentity_eta_add_mul_exponent`, `davenport_prod_le_eta_add_mul_exponent` | `DavenportProject/Transfer/BlockBound.lean` |
| `κ₀(G;K)=D(G)`; `κ_t(G;K)≤(t+1)D(G)` | `kappa_zero_eq_davenport`, `hasIncidenceIdentity_mul_davenport`, `kappa_le_mul_davenport` | `DavenportProject/InvariantBounds.lean` |
| Extension from an indexed subsequence | `HasIncidenceIdentity.of_embedding` | `DavenportProject/Identities/Extension.lean` |
| Remark 4.2: `κ₁(C₂³;𝔽₂)=5` | `kappa_cube_two_zmod_two_one` | `DavenportProject/CharacteristicTwo.lean` |
| Proposition 4.1 | `le_kappa_cube` | `DavenportProject/Sharpness.lean` |
| Lemma 5.1(1), (2) | `hasIncidenceIdentity_cube_three_ten`, `card_support_le_of_isShortZeroFree_cube_three` | `DavenportProject/Bases/CubeThree/Identity.lean`, `Support.lean` |
| Lemma 5.2 | `exists_large_zeroSet_cube_three` | `DavenportProject/Bases/CubeThree/LongZeroSet.lean` |
| Lemma 5.3: fourteen terms, eighteen terms (5.3(1) and 5.3(2) in the sources) | `hasIncidenceIdentity_cube_four_fourteen`, `hasIncidenceIdentity_cube_four_eighteen` | `DavenportProject/Bases/CubeFour/Quaternary.lean` |
| Section 5.3 eighteen-term example (sequence, zero sets, vector identity and quadratic lift) | `QuaternaryExample.sequence`, `sum_sequence`, `no_short_zero`, `no_long_zero`, `no_three_disjoint`, `B_zero`, `five_zero_sets`, `indicator_identity`, `remainder_identity`, `quadratic_identity`, `quadratic_certificate_check` (all in `QuaternaryExample`) | `DavenportProject/Examples/QuaternaryEighteen.lean` |
| `η(C_4^3) ≤ 22` (Harborth, cited in the paper) | `not_isShortZeroFree_cube_four` | `DavenportProject/Bases/CubeFour/Eta.lean` |
| Theorem B | `hasIncidenceIdentity_cube`, `kappa_cube_le`, `kappa_cube_eq` | `DavenportProject/TheoremB.lean` |
| Eq. (6.1) | `CorollaryC.davenport_cube_prod_le` | `DavenportProject/CorollaryC.lean` |
| Corollary C | `davenport_zmod_prod_three`, `davenport_cube_three_mul_prime_pow`, `davenport_cube_four_mul_prime_pow` | `DavenportProject/CorollaryC.lean` |
| Numerical instances of Corollary C, among them `D(C_15^3) = 43` and `D(C_3 ⊕ C_15 ⊕ C_75) = 91`, which the paper works out | `davenport_cube_fifteen`, `davenport_cube_twenty`, `davenport_cube_twentyOne`, `davenport_cube_twentyEight`, `davenport_cube_thirtySix`, `davenport_zmod_three_fifteen_seventyFive`, `davenport_zmod_four_twenty_hundred` | `DavenportProject/CorollaryC.lean` |

The cases `m = 2, 3, 4` of Theorem B are in `DavenportProject/Bases/CubeTwo.lean`,
`Bases/CubeThree.lean` and `Bases/CubeFour.lean`.

Two results that the paper cites are proved here: Olson's theorem and Harborth's bound
`η(C_4^3) ≤ 22`, whose existing pigeonhole proof is unchanged. The standard invariant `η` is now
defined, and Remarks 3.2 and 4.2 and the eighteen-term example are formalized. Remaining out of
scope: optional Remark 3.3, conjecture (1.1), and a separate definition of `D*` (the required
basis lower bounds are formalized).

## Relation to the paper

The ordinary proofs follow version 4: Theorem A evaluates the incidence identity at the
zero-sum indicator; Proposition 4.1 uses the integer triangular factorization with a
combinatorial block count; Lemma 5.1(2) uses affine-plane incidence counting. Lemma 2.2(2)
uses finite differences and Lemma 2.2(3) uses complement-degree cancellation. Section 5.1
exposes the Fano counts and weights. The finite-base reductions follow the paper's order.

The remaining differences are:

- **Lemma 5.1(1) and Lemma 5.3.** The unchanged finite enumerations and certificates use
  normal forms different from Appendix A's two enumerations; see the counts below.
- **Cited results.** Lean supplies proofs of Olson's theorem and Harborth's bound; the paper
  cites them. The Harborth proof has been left unchanged as requested.

The old support enumeration is retained under
`card_support_le_of_isShortZeroFree_cube_three_by_enumeration` as a redundant cross-check.
It enumerates increasing admissible code sets, without Appendix A.1's fixed-basis
normalization; it does not state Table 2's counts. The main support theorem, Lemma 5.2,
the ternary short-zero bound and Theorem B use the affine-plane proof.

The supplement has a section on this repository; its descriptions of the former proof
routes and out-of-scope items need updating for this branch.

## Trust and axioms

`python3 scripts/check_statements.py` checks 76 declarations in `statements.json`.
The original 43 entries and hashes are unchanged; 33 new paper-facing declarations
cover the added results, example data, and redundant support cross-check:

- **Statements.** It elaborates each declaration and compares a hash of its fully explicit form
  with the recorded hash. A match means the statement is unchanged from that recorded interface.
- **Axioms.** It checks which axioms each declaration depends on.

The axioms are:

- `propext`, `Classical.choice` and `Quot.sound` for every result that does not depend on
  Lemma 5.3 (definitions and finite checks may use fewer). Lemma 5.1(2) now follows the
  geometric proof; its small finite geometry facts and the retained redundant enumeration
  are checked by the kernel (`decide +kernel`). The new worked example also uses only kernel checks.
- The same three plus the axioms generated by `native_decide`: 7 for Lemma 5.3(1), and 13 for
  Lemma 5.3(2) and the results that use it (Theorem B and Corollary C). The finite input of Lemma 5.3 is too large for the kernel. It
  is evaluated by compiled code in 13 Boolean checks
  (`DavenportProject/Bases/CubeFour/Checks*`) over the Mathlib-free library `DavenportCompute`.
  These checks trust the Lean compiler, its bundled C compiler and the runtime, in addition to
  the kernel.

What is proved in Lean about the Lemma 5.3 computation:

- the certificate checker is sound (`CubeFour.hasIncidenceIdentity_of_check`);
- the enumeration of normalized short-zero-free sequences is complete
  (`CubeFour.leaf_of_prefixes`);
- every sequence can be brought into normal form by an injective additive map
  (`CubeFour.exists_isNormal`).

The certificates themselves (`DavenportCompute/Data.lean`) and the code that searches for them
(`DavenportCompute/Oracle.lean`) are untrusted: every certificate is re-checked before use.

## Finite computations

For Lemma 5.1(1), the frozen table has 3,382 cases: 2,209 certificates from a disjoint pair
(and its union), 1,137 five-set certificates and 36 seven-set certificates, all with
coefficients `±1`.

### Lemma 5.3

The Lean proof uses a different normal form from the paper's two enumerations (Appendix A.2 and A.3): the
standard basis vectors are chosen among support terms of maximal multiplicity. The unchanged enumerator contains 562,180
fourteen-term and 128,592 eighteen-term cases, before its easy-case reductions.

| Cases | 14 terms | 18 terms |
|---|---|---|
| Closed by disjoint zero sets or a long zero set | 525,719 | 126,240 |
| Use a stored certificate | 36,461 | 2,352 |
| Orbits of those cases (the paper's counts) | 6,963 | 64 |

Of the 6,963 affine certificates, 6,955 have five zero sets and coefficients `±1`. The
other eight stored certificates use 7, 9, 13 or 15 zero sets, with coefficient absolute
values at most 5. These are properties of the stored certificates, not minimality claims.
Each of the 64 quadratic certificates is the lift of a five-set affine identity on the
complement of a zero set; it has eleven zero sets and coefficients `±1`, as in the paper.
`scripts/l53/` contains the programs that produced the tables, with instructions to regenerate
them. They also reproduce the paper's Table 3 counts with a fixed support basis: 24,445,377 and
1,267,272.

## Building

The toolchain is `leanprover/lean4:v4.36.0-rc1` (see `lean-toolchain`). Mathlib is pinned to
`d6b19107529f14ba04640221cf560d767c81c8e9` in `lake-manifest.json`.

```sh
lake exe cache get                     # download the Mathlib build cache
lake build                             # build the library
lake build DavenportCompute            # explicitly build the computation library
python3 scripts/check_statements.py    # check the statements and their axioms
```

`DavenportCompute` is compiled to native code (`precompileModules`); Lean's bundled C toolchain is
enough. Build time depends on hardware and load; a fresh project build can reuse the pinned
Mathlib cache. The thirteen native checks and the ordinary kernel checks are part of the build.

## Layout

| Path | Contents |
|---|---|
| `DavenportProject/Defs.lean`, `Invariants.lean` | definitions, `D(G)`, `κ_t(G; K)` |
| `DavenportProject/Identities/` | Section 2: Lemmas 2.1 and 2.2 |
| `DavenportProject/Transfer/` | Section 3: Lemma 3.1, Olson's theorem, Theorem A and the `η` block bound |
| `DavenportProject/Sharpness.lean`, `Sharpness/BlockCount.lean`, `CharacteristicTwo.lean` | Section 4: Proposition 4.1 and Remark 4.2 |
| `DavenportProject/Bases/` | Section 5: the cubes `C_2^3`, `C_3^3` (Lemmas 5.1, 5.2) and `C_4^3` (Lemma 5.3) |
| `DavenportProject/TheoremB.lean`, `CorollaryC.lean` | Theorem B; Section 6: Corollary C and numerical instances |
| `DavenportCompute/` | the native computation library of Lemma 5.3 |
| `statements.json`, `scripts/check_statements.py` | the statement and axiom check |
| `.github/workflows/` | CI: build and statement check |
| `scripts/l53/` | untrusted generators of the Lemma 5.3 certificate tables |

## License and citation

Apache License 2.0 (`LICENSE`). If you use this work, please cite the paper (see `CITATION.cff`).
