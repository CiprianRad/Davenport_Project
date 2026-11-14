/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.ZMod.Defs

/-!
# Integral zero-sum incidence identities and Davenport constants in rank three

The statements of the main results of C. G. Pop, G. C. Rad and G. C. Țurcaș, *Integral zero-sum
incidence identities and Davenport constants in rank three* (2026). The definitions are copied
verbatim from the formalization (`DavenportProject/Defs.lean` and
`DavenportProject/Invariants.lean`); Comparator checks that `Solution.lean` proves exactly these
statements.

A finite sequence over an abelian group `G` is a map `u : ι → G` from a finite index type, so equal
terms at different positions are different terms. A *zero set* of `u` is a nonempty set of
positions whose terms sum to zero.

* `davenport G` is the Davenport constant `D(G)`: the least `L` such that every sequence of `L`
  terms has a zero set.
* An *incidence identity of degree `t`* (an `𝓘_t`-identity) of `u` over a commutative ring `R`
  is a family `(c_E)` indexed by the zero sets of `u` with `∑_E c_E = 1` and `∑_{E ⊇ J} c_E = 0`
  for every set `J` of `1 ≤ |J| ≤ t` positions (eq. (1.3) of the paper). It is *integral* if
  `R = ℤ`.
* `kappa G K t` is `κ_t(G; K)`: the least `N` such that no sequence of `N` terms over `G` has a
  separator of degree at most `t` over the field `K`, i.e. a polynomial `P` in the positions of
  total degree at most `t` with `P(0) = 1` and `P(𝟙_E) = 0` for every zero set `E`. By Lemma 2.1 of
  the paper, a sequence has no separator over `K` exactly when it has an `𝓘_t`-identity over `K`.

The results:

* **Theorem A** (`davenport_prod_le_of_hasIncidenceIdentity_zmod`, `…_int`): if every sequence of
  `L t` terms over a finite abelian group `Q` has an `𝓘_t`-identity over `𝔽_p` (or over `ℤ`), then
  `D(Q ⊕ H) ≤ L (D(H) - 1)` for every finite abelian `p`-group `H`.
* **Theorem B** (`hasIncidenceIdentity_cube`, `kappa_cube_le`, `kappa_cube_eq`): for
  `m = 2, 3, 4`, every sequence of `m (t + 3) - 2` terms over `C_m^3` has an integral
  `𝓘_t`-identity, hence `κ_t(C_m^3; K) ≤ m (t + 3) - 2` for every field `K`, with equality when
  the characteristic of `K` is `0` or does not divide `m`.
* **Corollary C** (`davenport_zmod_prod_three`): for `m = 2, 3, 4`, a prime `p` not dividing `m` and
  `0 ≤ a ≤ b ≤ c`, `D(C_{m p^a} ⊕ C_{m p^b} ⊕ C_{m p^c}) = m (p^a + p^b + p^c) - 2`. In particular
  `D(C_15^3) = 43` and `D(C_20^3) = 58` (`davenport_cube_fifteen`, `davenport_cube_twenty`).

`exists_length_forcing_zeroSet` and `exists_length_without_separator` say that `davenport` and
`kappa` are well defined; they are proved in the solution as well. The hypothesis `[NeZero m]` in
Theorem B and Corollary C only makes `ZMod m` a finite type, so that `davenport` and `kappa` apply;
it follows from `hm`.
-/

@[expose] public section

namespace DavenportProject

open Finset

/-! ## Definitions (verbatim from `DavenportProject/Defs.lean`) -/

section Defs

variable {G : Type*} [AddCommGroup G] {ι : Type*}

/-- A *zero set* of the indexed sequence `u`: a nonempty set `E` of positions with
`∑ i ∈ E, u i = 0`. -/
def IsZeroSet (u : ι → G) (E : Finset ι) : Prop :=
  E.Nonempty ∧ ∑ i ∈ E, u i = 0

open Classical in
/-- The finite set `𝒵(u)` of zero sets of `u`. -/
noncomputable def zeroSets [Fintype ι] (u : ι → G) : Finset (Finset ι) :=
  univ.filter (IsZeroSet u)

open Classical in
/-- `c` is an *`𝓘_t`-identity over `R`* for `u` (eq. (1.3)): only the values of `c` on the
zero sets of `u` are read, and they satisfy `∑_E c_E = 1` and `∑_{E ⊇ J} c_E = 0` for every
`J` with `1 ≤ |J| ≤ t`. -/
def IsIncidenceIdentity (R : Type*) [CommRing R] [Fintype ι] (u : ι → G) (t : ℕ)
    (c : Finset ι → R) : Prop :=
  ∑ E ∈ zeroSets u, c E = 1 ∧
    ∀ J : Finset ι, 1 ≤ #J → #J ≤ t → ∑ E ∈ zeroSets u with J ⊆ E, c E = 0

/-- `u` has an `𝓘_t`-identity over `R`; over `R = ℤ` this is an *integral* identity. -/
def HasIncidenceIdentity (R : Type*) [CommRing R] [Fintype ι] (u : ι → G) (t : ℕ) : Prop :=
  ∃ c : Finset ι → R, IsIncidenceIdentity R u t c

/-- A *separator of degree at most `t`* over the field `K` for `u`: a polynomial of total degree at
most `t` with `P(0) = 1` and `P(𝟙_E) = 0` for every zero set `E`. -/
def IsSeparator (K : Type*) [Field K] (u : ι → G) (t : ℕ) (P : MvPolynomial ι K) : Prop :=
  P.totalDegree ≤ t ∧ MvPolynomial.eval 0 P = 1 ∧
    ∀ E : Finset ι, IsZeroSet u E → MvPolynomial.eval ((E : Set ι).indicator 1) P = 0

/-- `u` has a separator of degree at most `t` over `K`. -/
def HasSeparator (K : Type*) [Field K] (u : ι → G) (t : ℕ) : Prop :=
  ∃ P : MvPolynomial ι K, IsSeparator K u t P

end Defs

/-! ## The invariants (verbatim from `DavenportProject/Invariants.lean`) -/

section Invariants

-- As in `Invariants.lean`, this fixes the universe names of `davenport` and `kappa`.
variable {G : Type*} [AddCommGroup G] {ι : Type*}

/-- Every long enough sequence has a zero set; this makes `davenport` well defined. -/
theorem exists_length_forcing_zeroSet (G : Type*) [AddCommGroup G] [Finite G] :
    ∃ L : ℕ, ∀ u : Fin L → G, ∃ E, IsZeroSet u E := by
  sorry

open Classical in
/-- The *Davenport constant* `D(G)`: the least `L` such that every sequence of `L` terms
over `G` has a nonempty zero-sum subsequence. -/
noncomputable def davenport (G : Type*) [AddCommGroup G] [Finite G] : ℕ :=
  Nat.find (exists_length_forcing_zeroSet G)

/-- For every `t`, long enough sequences have no separator of degree at most `t`; this makes
`kappa` well defined. -/
theorem exists_length_without_separator (G : Type*) [AddCommGroup G] [Finite G]
    (K : Type*) [Field K] (t : ℕ) :
    ∃ N : ℕ, ∀ u : Fin N → G, ¬ HasSeparator K u t := by
  sorry

open Classical in
/-- `κ_t(G;K)`: the least `N` such that no sequence of `N` terms over `G` has a separator of
degree at most `t` over `K`. -/
noncomputable def kappa (G : Type*) [AddCommGroup G] [Finite G] (K : Type*) [Field K]
    (t : ℕ) : ℕ :=
  Nat.find (exists_length_without_separator G K t)

end Invariants

/-! ## Theorem A -/

/-- **Theorem A** (identities over `𝔽_p`): if every sequence of `L t` terms over `Q` has an
`𝓘_t`-identity over `ZMod p`, then `D(Q ⊕ H) ≤ L (D(H) - 1)` for every finite abelian `p`-group
`H`. -/
theorem davenport_prod_le_of_hasIncidenceIdentity_zmod (Q : Type*) [AddCommGroup Q]
    [Finite Q] (p : ℕ) [Fact p.Prime] (L : ℕ → ℕ)
    (hL : ∀ t, ∀ u : Fin (L t) → Q, HasIncidenceIdentity (ZMod p) u t)
    (H : Type*) [AddCommGroup H] [Finite H] (hH : IsPGroup p (Multiplicative H)) :
    davenport (Q × H) ≤ L (davenport H - 1) := by
  sorry

/-- **Theorem A** (integral identities): if every sequence of `L t` terms over `Q` has an integral
`𝓘_t`-identity, then `D(Q ⊕ H) ≤ L (D(H) - 1)` for every prime `p` and every finite abelian
`p`-group `H`. -/
theorem davenport_prod_le_of_hasIncidenceIdentity_int (Q : Type*) [AddCommGroup Q]
    [Finite Q] (L : ℕ → ℕ) (hL : ∀ t, ∀ u : Fin (L t) → Q, HasIncidenceIdentity ℤ u t)
    (p : ℕ) [Fact p.Prime]
    (H : Type*) [AddCommGroup H] [Finite H] (hH : IsPGroup p (Multiplicative H)) :
    davenport (Q × H) ≤ L (davenport H - 1) := by
  sorry

/-! ## Theorem B -/

/-- **Theorem B**: for `m = 2, 3, 4` and every `t`, every sequence of `m (t + 3) - 2` terms over
`C_m^3 = (ZMod m)^3` has an integral `𝓘_t`-identity. -/
theorem hasIncidenceIdentity_cube (m : ℕ) (hm : m = 2 ∨ m = 3 ∨ m = 4) (t : ℕ)
    (u : Fin (m * (t + 3) - 2) → (Fin 3 → ZMod m)) :
    HasIncidenceIdentity ℤ u t := by
  sorry

/-- **Theorem B**: for `m = 2, 3, 4`, every `t` and every field `K`,
`κ_t(C_m^3; K) ≤ m (t + 3) - 2`. -/
theorem kappa_cube_le (m : ℕ) [NeZero m] (hm : m = 2 ∨ m = 3 ∨ m = 4) (t : ℕ)
    (K : Type*) [Field K] :
    kappa (Fin 3 → ZMod m) K t ≤ m * (t + 3) - 2 := by
  sorry

/-- **Theorem B**: for `m = 2, 3, 4`, every `t` and every field `K` of characteristic `0` or not
dividing `m`, `κ_t(C_m^3; K) = m (t + 3) - 2`. -/
theorem kappa_cube_eq (m : ℕ) [NeZero m] (hm : m = 2 ∨ m = 3 ∨ m = 4) (t : ℕ)
    (K : Type*) [Field K] (hK : ringChar K = 0 ∨ ¬ ringChar K ∣ m) :
    kappa (Fin 3 → ZMod m) K t = m * (t + 3) - 2 := by
  sorry

/-! ## Corollary C -/

/-- **Corollary C**: for `m = 2, 3, 4`, a prime `p` not dividing `m` and `a ≤ b ≤ c`,
`D(C_{m p^a} ⊕ C_{m p^b} ⊕ C_{m p^c}) = m (p^a + p^b + p^c) - 2`. -/
theorem davenport_zmod_prod_three (m : ℕ) [NeZero m] (hm : m = 2 ∨ m = 3 ∨ m = 4) (p : ℕ)
    [Fact p.Prime] (hpm : ¬ p ∣ m) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    davenport (ZMod (m * p ^ a) × ZMod (m * p ^ b) × ZMod (m * p ^ c)) =
      m * (p ^ a + p ^ b + p ^ c) - 2 := by
  sorry

/-- `D(C_15^3) = 43`: the case `m = 3`, `p = 5`, `a = b = c = 1` of Corollary C. -/
theorem davenport_cube_fifteen : davenport (Fin 3 → ZMod 15) = 43 := by
  sorry

/-- `D(C_20^3) = 58`: the case `m = 4`, `p = 5`, `a = b = c = 1` of Corollary C. -/
theorem davenport_cube_twenty : davenport (Fin 3 → ZMod 20) = 58 := by
  sorry

end DavenportProject
