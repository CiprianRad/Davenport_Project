# Davenport constants in rank three, formalized in Lean 4

[![CI](https://github.com/CiprianRad/Davenport_Project/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/CiprianRad/Davenport_Project/actions/workflows/lean_action_ci.yml)

This repository is the Lean 4 companion of the paper

> C. G. Pop, G. C. Rad and G. C. Țurcaș, *Integral zero-sum incidence identities and Davenport
> constants in rank three* (manuscript, November 2026).

The paper proves that

```math
\mathsf D\bigl(C_{mp^a}\oplus C_{mp^b}\oplus C_{mp^c}\bigr)=m\,(p^a+p^b+p^c)-2
```

for m = 2, 3, 4, every prime p not dividing m, and all integers 0 ≤ a ≤ b ≤ c. Among these values
are D(C₁₅³) = 43 and D(C₂₀³) = 58, the two smallest cubes that the classical results leave open.
In Lean the first one reads

```lean
theorem davenport_cube_fifteen : davenport (Fin 3 → ZMod 15) = 43
```

Every lemma, proposition, theorem and corollary of the paper is stated and proved here, together
with the definitions they need, Remarks 3.2 and 4.2 and the worked example of Section 5.3. We have
tried to make the formal proofs follow the written ones step by step, so that the two can be read
side by side. Statement numbers are those of the manuscript.

## Finding your way

Most visitors come with one of these questions.

- *I have the paper open. Where is this statement in Lean?* See
  [From the paper to Lean](#from-the-paper-to-lean).
- *Are the formal proofs the proofs of the paper?* See
  [The proofs and the paper](#the-proofs-and-the-paper).
- *How much of this do I have to believe?* See [What is trusted](#what-is-trusted).
- *How do I run it?* See [Building and checking](#building-and-checking).
- *What exactly did the computer compute?* See
  [The finite computations](#the-finite-computations).
- *Where is the file I am looking for?* See [Layout](#layout).

## Reading the statements

If you have never read Lean, these few conventions are enough for everything in the tables below.

- A sequence of `N` terms over a group `G` is a function `u : Fin N → G`. Terms are indexed, as in
  the paper: equal elements at different positions are different terms.
- The group C_m³ is `Fin 3 → ZMod m`, and C_a ⊕ C_b ⊕ C_c is `ZMod a × ZMod b × ZMod c`.
- `IsZeroSet u E` says that `E` is a nonempty set of positions whose terms sum to zero.
- `HasIncidenceIdentity R u t` says that `u` has an incidence identity of degree `t` with
  coefficients in `R`. Integral identities are the case `R = ℤ`.
- `davenport G` is D(G), `kappa G K t` is κ_t(G; K) and `eta G` is η(G). Each is defined as a least
  length; `davenport_eq_iff`, `kappa_eq_iff` and `eta_eq_iff` say what that means.

All names are in the namespace `DavenportProject`. They are long, but they try to say what they
prove.

## From the paper to Lean

### Definitions

| In the paper | In Lean | File |
|---|---|---|
| Zero sets | `IsZeroSet`, `zeroSets` | [`Defs.lean`](DavenportProject/Defs.lean) |
| Incidence identities, eq. (1.3) | `IsIncidenceIdentity`, `HasIncidenceIdentity` | [`Defs.lean`](DavenportProject/Defs.lean) |
| Separators | `IsSeparator`, `HasSeparator` | [`Defs.lean`](DavenportProject/Defs.lean) |
| Short-zero-free sequences | `IsShortZeroFree` | [`Defs.lean`](DavenportProject/Defs.lean) |
| The Davenport constant D(G) | `davenport` | [`Invariants.lean`](DavenportProject/Invariants.lean) |
| The invariant κ_t(G; K) | `kappa` | [`Invariants.lean`](DavenportProject/Invariants.lean) |
| The invariant η(G) | `eta` | [`Transfer/BlockBound.lean`](DavenportProject/Transfer/BlockBound.lean) |

### Sections 1 and 2: identities and the three constructions

| In the paper | In Lean | File |
|---|---|---|
| κ₀(G; K) = D(G) | `kappa_zero_eq_davenport` | [`InvariantBounds.lean`](DavenportProject/InvariantBounds.lean) |
| Lemma 2.1(1) | `isIncidenceIdentity_iff_eval` | [`Identities/Evaluation.lean`](DavenportProject/Identities/Evaluation.lean) |
| Lemma 2.1(2) | `IsIncidenceIdentity.intCast` | [`Identities/Evaluation.lean`](DavenportProject/Identities/Evaluation.lean) |
| Lemma 2.1(3) | `hasIncidenceIdentity_iff_not_hasSeparator` | [`Identities/Duality.lean`](DavenportProject/Identities/Duality.lean) |
| An identity on a subsequence extends to the whole sequence | `HasIncidenceIdentity.of_embedding` | [`Identities/Extension.lean`](DavenportProject/Identities/Extension.lean) |
| κ_t(G; K) ≤ (t + 1) D(G) | `kappa_le_mul_davenport` | [`InvariantBounds.lean`](DavenportProject/InvariantBounds.lean) |
| Lemma 2.2(1) | `hasIncidenceIdentity_of_pairwise_disjoint` | [`Identities/Operations.lean`](DavenportProject/Identities/Operations.lean) |
| Lemma 2.2(2) | `hasIncidenceIdentity_of_disjoint_zeroSet` | [`Identities/Operations.lean`](DavenportProject/Identities/Operations.lean) |
| Lemma 2.2(3) | `hasIncidenceIdentity_of_ssubset_zeroSet` | [`Identities/Operations.lean`](DavenportProject/Identities/Operations.lean) |

The two degree cancellations behind Lemma 2.2(2) and (3) are in
[`Identities/PolynomialLifting.lean`](DavenportProject/Identities/PolynomialLifting.lean).

### Section 3: the transfer principle

| In the paper | In Lean | File |
|---|---|---|
| Lemma 3.1 | `exists_multilinear_zeroSum_indicator` | [`Transfer/Indicator.lean`](DavenportProject/Transfer/Indicator.lean) |
| Olson's theorem | `davenport_pi_zmod_prime_pow` | [`Transfer/Olson.lean`](DavenportProject/Transfer/Olson.lean) |
| Theorem A, identities over 𝔽_p | `davenport_prod_le_of_hasIncidenceIdentity_zmod` | [`Transfer/TheoremA.lean`](DavenportProject/Transfer/TheoremA.lean) |
| Theorem A, integral identities | `davenport_prod_le_of_hasIncidenceIdentity_int` | [`Transfer/TheoremA.lean`](DavenportProject/Transfer/TheoremA.lean) |
| Remark 3.2 and the bound (1.2) | `davenport_prod_le_eta_add_mul_exponent` | [`Transfer/BlockBound.lean`](DavenportProject/Transfer/BlockBound.lean) |

The nilpotence of the augmentation ideal, on which Lemma 3.1 and Olson's theorem rest, is in
[`Transfer/Augmentation.lean`](DavenportProject/Transfer/Augmentation.lean).

### Section 4: sharpness

| In the paper | In Lean | File |
|---|---|---|
| Proposition 4.1 | `le_kappa_cube` | [`Sharpness.lean`](DavenportProject/Sharpness.lean) |
| Remark 4.2 | `kappa_cube_two_zmod_two_one` | [`CharacteristicTwo.lean`](DavenportProject/CharacteristicTwo.lean) |

The numbers `a_{j,i}` in the proof of Proposition 4.1 are `Sharpness.blockSubsetCount`, in
[`Sharpness/BlockCount.lean`](DavenportProject/Sharpness/BlockCount.lean).

### Section 5: the quotients C₂³, C₃³ and C₄³

Apart from the last row, the files of this section are in
[`DavenportProject/Bases/`](DavenportProject/Bases).

| In the paper | In Lean | File |
|---|---|---|
| Theorem B, m = 2 | `Bases.hasIncidenceIdentity_cube_two` | [`CubeTwo.lean`](DavenportProject/Bases/CubeTwo.lean) |
| Lemma 5.1(1) | `hasIncidenceIdentity_cube_three_ten` | [`CubeThree/Identity.lean`](DavenportProject/Bases/CubeThree/Identity.lean) |
| Lemma 5.1(2) | `card_support_le_of_isShortZeroFree_cube_three` | [`CubeThree/Support.lean`](DavenportProject/Bases/CubeThree/Support.lean) |
| Lemma 5.2 | `exists_large_zeroSet_cube_three` | [`CubeThree/LongZeroSet.lean`](DavenportProject/Bases/CubeThree/LongZeroSet.lean) |
| Theorem B, m = 3 | `Bases.hasIncidenceIdentity_cube_three` | [`CubeThree.lean`](DavenportProject/Bases/CubeThree.lean) |
| Lemma 5.3, 14 terms | `hasIncidenceIdentity_cube_four_fourteen` | [`CubeFour/Quaternary.lean`](DavenportProject/Bases/CubeFour/Quaternary.lean) |
| Lemma 5.3, 18 terms | `hasIncidenceIdentity_cube_four_eighteen` | [`CubeFour/Quaternary.lean`](DavenportProject/Bases/CubeFour/Quaternary.lean) |
| η(C₄³) ≤ 22 | `not_isShortZeroFree_cube_four` | [`CubeFour/Eta.lean`](DavenportProject/Bases/CubeFour/Eta.lean) |
| Theorem B, m = 4 | `Bases.hasIncidenceIdentity_cube_four` | [`CubeFour.lean`](DavenportProject/Bases/CubeFour.lean) |
| Theorem B | `hasIncidenceIdentity_cube`, `kappa_cube_le`, `kappa_cube_eq` | [`TheoremB.lean`](DavenportProject/TheoremB.lean) |

The plane counting behind Lemma 5.1(2) is in
[`PlaneGeometry.lean`](DavenportProject/Bases/CubeThree/PlaneGeometry.lean) and
[`Planes.lean`](DavenportProject/Bases/CubeThree/Planes.lean).

The eighteen-term example of Section 5.3 has a file of its own,
[`Examples/QuaternaryEighteen.lean`](DavenportProject/Examples/QuaternaryEighteen.lean). It
contains the sequence, its sum (0, 3, 1), the facts that it has no zero set of at most four or of
at least fifteen terms and no three disjoint zero sets, the zero set B, the five zero sets
disjoint from B with their identity, and the quadratic identity that Lemma 2.2(2) makes out of
them (`QuaternaryExample.quadratic_identity`).

### Section 6: Davenport constants

| In the paper | In Lean | File |
|---|---|---|
| The bound (6.1) | `CorollaryC.davenport_cube_prod_le` | [`CorollaryC.lean`](DavenportProject/CorollaryC.lean) |
| Corollary C | `davenport_zmod_prod_three` | [`CorollaryC.lean`](DavenportProject/CorollaryC.lean) |
| `D(C_{3p^a}^3) = 9p^a - 2` | `davenport_cube_three_mul_prime_pow` | [`CorollaryC.lean`](DavenportProject/CorollaryC.lean) |
| `D(C_{4p^a}^3) = 12p^a - 2` | `davenport_cube_four_mul_prime_pow` | [`CorollaryC.lean`](DavenportProject/CorollaryC.lean) |
| D(C₁₅³) = 43 and D(C₂₀³) = 58 | `davenport_cube_fifteen`, `davenport_cube_twenty` | [`CorollaryC.lean`](DavenportProject/CorollaryC.lean) |
| D(C₃ ⊕ C₁₅ ⊕ C₇₅) = 91 | `davenport_zmod_three_fifteen_seventyFive` | [`CorollaryC.lean`](DavenportProject/CorollaryC.lean) |

A few more numerical values sit next to these: 61, 82 and 106 for the cubes of C₂₁, C₂₈ and C₃₆,
and 122 for C₄ ⊕ C₂₀ ⊕ C₁₀₀.

## The proofs and the paper

The formal proofs follow the written ones. Theorem A evaluates the identity at the zero-sum
indicator of Lemma 3.1. Proposition 4.1 factors the matrix of binomial coefficients over the
integers, by counting subsets according to the blocks they meet. Lemma 5.1(2) counts the
incidences of a cap with the 39 affine planes of 𝔽₃³. Lemma 2.2(2) and (3) use the finite
difference and the complement, and Section 5.1 uses the Fano plane with one point removed. Each of
these proofs carries a docstring naming the statement and the section of the paper, and the longer
ones are cut into lemmas that match the steps of the written argument.

Lean and the paper part ways in three places, all on purpose.

1. **The two computer-assisted statements.** Lemma 5.1(1) and Lemma 5.3 rest on finite
   enumerations. The paper describes its own in Appendix A. The Lean proof uses another one, with
   a normal form of its own, and proves inside Lean that it misses nothing. The reductions that
   come before the enumeration are those of the paper. The numbers are in
   [The finite computations](#the-finite-computations).
2. **Two results that the paper quotes are proved here.** Olson's theorem is proved by the
   nilpotence argument of Section 3, and the bound η(C₄³) ≤ 22 by a pigeonhole argument through
   reduction modulo two.
3. **Lemma 5.1(2) is proved twice.** The proof by plane counting is the one on which everything
   else depends. A second proof, by an enumeration that Lean's kernel evaluates, is kept as a
   redundant check under the name `card_support_le_of_isShortZeroFree_cube_three_by_enumeration`.
   It runs over increasing admissible sets of points; it is not the enumeration of Appendix A.1
   and does not produce the counts of Table 2.

Not formalized: Remark 3.3, the conjecture (1.1), and D* as a definition of its own. The basis
lower bounds that the proofs use are formalized.

The supplement to the paper has a section about this repository.

## What is trusted

[`statements.json`](statements.json) lists the 76 declarations that make up the formal
counterpart of the paper: the definitions, the results, and the data of the worked example. For
each of them the script [`scripts/check_statements.py`](scripts/check_statements.py) does two
things. It compares a hash of the fully elaborated statement with the recorded one, so that no
statement can change unnoticed. And it lists the axioms on which the proof depends.

- Everything that does not depend on Lemma 5.3 uses only the three standard axioms of Lean:
  `propext`, `Classical.choice` and `Quot.sound`. This includes Lemma 5.1 and the worked example,
  whose finite parts are evaluated by Lean's kernel (`decide +kernel`).
- Lemma 5.3 needs a computation that is too large for the kernel. It is run as compiled code
  (`native_decide`), in thirteen Boolean checks: seven for the fourteen-term statement, and all
  thirteen for the eighteen-term one. The checks are in
  [`Bases/CubeFour/Checks.lean`](DavenportProject/Bases/CubeFour/Checks.lean) and the folder next
  to it. Lemma 5.3, Theorem B and Corollary C therefore also trust the Lean compiler, its bundled
  C compiler and the runtime.

Around those thirteen checks, the following is proved in Lean in the ordinary way:

- the certificate checker is sound (`CubeFour.hasIncidenceIdentity_of_check`);
- the enumeration reaches every normalized short-zero-free sequence (`CubeFour.leaf_of_prefixes`);
- every sequence can be brought to normal form by an injective additive map
  (`CubeFour.exists_isNormal`).

The certificate tables in [`DavenportCompute/Data.lean`](DavenportCompute/Data.lean) and the
search in [`DavenportCompute/Oracle.lean`](DavenportCompute/Oracle.lean) are not trusted. Every
certificate is checked again before it is used, so a wrong table can only make the build fail.

## Building and checking

You need [Lean 4](https://lean-lang.org/install/) and, for the last step, Python 3.

```sh
lake exe cache get                     # download the compiled Mathlib
lake build                             # compile everything
python3 scripts/check_statements.py    # check statements and axioms
```

The toolchain is `leanprover/lean4:v4.36.0-rc1` (see [`lean-toolchain`](lean-toolchain)), and
Mathlib is pinned in [`lake-manifest.json`](lake-manifest.json). Once the Mathlib cache is in
place, the build takes about two minutes on a laptop; the thirteen native checks are part of it.
The last command should end with `76 declarations, 0 failure(s)`.

The library `DavenportCompute`, which holds the computation of Lemma 5.3, does not depend on
Mathlib and is compiled to native code. Lean's bundled C toolchain is enough for that.

## The finite computations

**Lemma 5.1(1).** Two repeated points of the support are sent to e₁ and e₂. This leaves 3,382
cases: 2,209 contain two disjoint zero sets, and 1,137 and 36 receive an explicit identity on five
and on seven zero sets. All coefficients are ±1, and the whole check is done by the kernel.

**Lemma 5.3.** The standard basis vectors are chosen among the terms of the support with the
largest multiplicity.

| | 14 terms | 18 terms |
|---|---:|---:|
| Normalized cases | 562,180 | 128,592 |
| Closed by disjoint zero sets or by a long zero set | 525,719 | 126,240 |
| Needing a stored certificate | 36,461 | 2,352 |
| Orbits of those under the linear group, as in the paper | 6,963 | 64 |

Of the 6,963 affine certificates, 6,955 have five zero sets and coefficients ±1. The other eight
representatives have no certificate of that shape. Theirs were found by an exact integer solver
and have between 7 and 15 zero sets, with coefficients up to 5 in absolute value. Each of the 64
quadratic certificates has eleven zero sets and coefficients ±1. It is a five-set affine identity
on the complement of a zero set, lifted by Lemma 2.2(2), just like the example of Section 5.3.

The programs that produced the tables are in [`scripts/l53/`](scripts/l53), with instructions for
running them again. On the way they recover two numbers of Table 3 of the paper, the 24,445,377
and 1,267,272 sequences with a fixed support basis.

## Layout

| Path | What is there |
|---|---|
| [`DavenportProject/Defs.lean`](DavenportProject/Defs.lean), [`Invariants.lean`](DavenportProject/Invariants.lean), [`InvariantBounds.lean`](DavenportProject/InvariantBounds.lean) | the definitions, D(G) and κ_t(G; K) |
| [`DavenportProject/Identities/`](DavenportProject/Identities) | Section 2: Lemmas 2.1 and 2.2 |
| [`DavenportProject/Transfer/`](DavenportProject/Transfer) | Section 3: Lemma 3.1, Olson's theorem, Theorem A, Remark 3.2 |
| [`DavenportProject/Sharpness.lean`](DavenportProject/Sharpness.lean), [`Sharpness/`](DavenportProject/Sharpness), [`CharacteristicTwo.lean`](DavenportProject/CharacteristicTwo.lean) | Section 4: Proposition 4.1 and Remark 4.2 |
| [`DavenportProject/Bases/`](DavenportProject/Bases) | Section 5: the cubes C₂³, C₃³ (Lemmas 5.1 and 5.2) and C₄³ (Lemma 5.3) |
| [`DavenportProject/Examples/`](DavenportProject/Examples) | the eighteen-term example of Section 5.3 |
| [`DavenportProject/TheoremB.lean`](DavenportProject/TheoremB.lean), [`CorollaryC.lean`](DavenportProject/CorollaryC.lean) | Theorem B, and Section 6 with Corollary C and the numerical values |
| [`DavenportCompute/`](DavenportCompute) | the computation library of Lemma 5.3 |
| [`statements.json`](statements.json), [`scripts/check_statements.py`](scripts/check_statements.py) | the check of the statements and of their axioms |
| [`scripts/l53/`](scripts/l53) | the programs that generated the certificate tables of Lemma 5.3 |
| [`.github/workflows/`](.github/workflows) | continuous integration: the build and the statement check |

## License and citation

The code is released under the Apache License 2.0, see [`LICENSE`](LICENSE). If you use it,
please cite the paper; the details are in [`CITATION.cff`](CITATION.cff).

If something here is unclear, or a statement does not say what you expected it to say, we would
like to know. Please open an issue.
