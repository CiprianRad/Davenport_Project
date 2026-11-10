/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Defs
import DavenportProject.Invariants
import DavenportProject.Bases.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import DavenportProject.Bases.CubeFour.Checks
import DavenportProject.Bases.CubeFour.Enumeration
import DavenportProject.Bases.CubeFour.Eta
import DavenportProject.Bases.CubeFour.Normalize
import DavenportProject.Identities.Operations

/-!
# Lemma 5.3

* `hasIncidenceIdentity_cube_four_fourteen` (Lemma 5.3(1)): every fourteen-term sequence over
  `C_4^3` has an integral `𝓘_1`-identity.
* `hasIncidenceIdentity_cube_four_eighteen` (Lemma 5.3(2)): every eighteen-term sequence over
  `C_4^3` has an integral `𝓘_2`-identity.

Short zero sets reduce to smaller cases through Lemma 2.2. Short-zero-free sequences are
normalized (`exists_sortedCodes`) and covered by the enumeration (`leaf_of_prefixes`), whose leaves
pass the certificate checks of `Bases.CubeFour.Checks`. The normalization differs from the paper's
projection-and-lift; the orbit counts of the hard cases agree with the paper (6,963 and 64).

The paper states Lemma 5.3 as one sentence; (1) and (2) are its fourteen-term and eighteen-term
assertions. Its two enumerations are in Appendix A.2 and A.3, with the counts in Table 3.
-/

public section

namespace DavenportProject

open Finset CubeFour DavenportCompute

/-!
## Proof of Lemma 5.3(1)

Proof (with a different normalization than the paper's; finite part by
`native_decide`):
* A zero set `E` with `#E ≤ 4` leaves at least ten terms outside it, which contain a zero set since
  `D(C_4^3) = 10`; the two disjoint zero sets give the identity by Lemma 2.2(1).
* Otherwise the sequence is short-zero-free. An injective additive map and a sorting reindexing
  turn it into a sorted code list that is normalized (`exists_sortedCodes`): the standard basis
  vectors are chosen among the terms with maximal multiplicities. The enumeration of all such
  lists (`DavenportCompute.gdfs`) is complete (`leaf_of_prefixes`), and its native evaluation
  (`Checks.top`, `Checks.chunks14`) shows that every normalized list passes `leaf14`: a
  certificate checked by `DavenportCompute.check`, whose soundness is
  `hasIncidenceIdentity_of_check`. Of the 562,180 normalized lists, 525,719 get two disjoint zero
  sets and 36,461 get a stored certificate of one of 6,963 orbits, moved by a linear map.
-/

/-- **Lemma 5.3, Section 5.3, fourteen-term reduction**: a zero set of at most four
positions leaves ten terms and hence a disjoint zero set. Lemma 2.2(1) gives the identity. -/
theorem CubeFour.hasIncidenceIdentity_one_of_card_le_four {u : Fin 14 → (Fin 3 → ZMod 4)}
    {E : Finset (Fin 14)} (hE : IsZeroSet u E) (hcard : #E ≤ 4) : HasIncidenceIdentity ℤ u 1 := by
  -- Delete the short zero set; Olson's D(C₄³) = 10 supplies a second zero set.
  obtain ⟨S, hS, hS10⟩ := exists_subset_card_eq (s := Eᶜ) (n := 10)
    (by rw [card_compl, Fintype.card_fin]; omega)
  let e := S.orderEmbOfFin hS10
  obtain ⟨F', hF'⟩ := ((davenport_eq_iff _ 10).1 Bases.davenport_cube_four).1
    (fun i => u (e i))
  let F := F'.map e.toEmbedding
  have hF : IsZeroSet u F := by
    refine ⟨hF'.1.map, ?_⟩
    rw [sum_map]
    exact hF'.2
  have hdisj : Disjoint E F := by
    rw [disjoint_iff_ne]
    rintro a ha b hb rfl
    obtain ⟨i, -, rfl⟩ := mem_map.1 hb
    exact (mem_compl.1 (hS (S.orderEmbOfFin_mem hS10 i))) ha
  -- The two disjoint zero sets give the weights +1,+1,-1 of Lemma 2.2(1).
  refine hasIncidenceIdentity_of_pairwise_disjoint u 1 ![E, F] ?_ ?_
  · intro k
    fin_cases k
    exacts [hE, hF]
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hdisj
    · exact hdisj.symm
    · exact absurd rfl hij

/-- **Lemma 5.3(1), Section 5.3** (finite computation): every fourteen-term
sequence over `C_4^3` has an integral `𝓘_1`-identity. -/
theorem hasIncidenceIdentity_cube_four_fourteen (u : Fin 14 → (Fin 3 → ZMod 4)) :
    HasIncidenceIdentity ℤ u 1 := by
  by_cases hs : ∃ E, IsZeroSet u E ∧ #E ≤ 4
  · obtain ⟨E, hE, hcard⟩ := hs
    exact hasIncidenceIdentity_one_of_card_le_four hE hcard
  · have hu : ∀ E, IsZeroSet u E → 4 < #E := fun E hE => not_le.1 fun h => hs ⟨E, hE, h⟩
    obtain ⟨φ, hφ, σ, c, hdec, hsort, hlt, hszf, hg, hn3⟩ := exists_sortedCodes u hu
    have hleaf := leaf_of_prefixes leaf14 4 (List.ofFn c) (by simp) hsort hlt hszf hg Checks.top
      (by simpa using Checks.chunks14)
    simp only [leaf14, hn3, Bool.not_true, Bool.false_or, List.reverse_reverse] at hleaf
    exact hasIncidenceIdentity_of_sortedCodes hφ hdec (hasIncidenceIdentity_of_check c _ hleaf)

/-!
## Proof of Lemma 5.3(2)

Proof (with a different normalization than the paper's; finite part by
`native_decide`), following the reductions of the paper:
* A zero set `B` with `#B ≤ 4` leaves at least fourteen terms outside it, which have an integral
  `𝓘_1`-identity by Lemma 5.3(1); Lemma 2.2(2) with `t = 2` applies.
* Three disjoint zero sets give a quadratic identity directly by Lemma 2.2(1).
* A zero set `Z` with at least fifteen positions contains fourteen positions properly;
  their affine identity lifts by Lemma 2.2(3).
* The remaining short-zero-free sequences become normalized sorted code lists
  (`exists_sortedCodes`). The unchanged complete enumeration (`Checks.top`, `Checks.chunks18`)
  supplies a checked quadratic certificate, retaining its long-zero alternative as redundant
  coverage. Of the 128,592 normalized lists, 126,240 have a long zero set and 2,352 receive a
  stored certificate from one of 64 linear orbits.
-/

/-- Lemma 5.3(1) over any index type with fourteen elements. -/
theorem CubeFour.hasIncidenceIdentity_of_card_eq_fourteen {ι : Type*} [Fintype ι]
    (h : Fintype.card ι = 14) (v : ι → (Fin 3 → ZMod 4)) : HasIncidenceIdentity ℤ v 1 := by
  let e : ι ≃ Fin 14 := Fintype.equivFinOfCardEq h
  have := hasIncidenceIdentity_comp_equiv _ e
    (hasIncidenceIdentity_cube_four_fourteen fun k => v (e.symm k))
  simpa using this

/-- A zero set of size at most four gives an integral `𝓘_2`-identity: fourteen terms outside it
have an `𝓘_1`-identity (Lemma 5.3(1)), and Lemma 2.2(2) applies. -/
theorem CubeFour.hasIncidenceIdentity_two_of_card_le_four {u : Fin 18 → (Fin 3 → ZMod 4)}
    {B : Finset (Fin 18)} (hB : IsZeroSet u B) (hcard : #B ≤ 4) : HasIncidenceIdentity ℤ u 2 := by
  obtain ⟨S, hS, hS14⟩ := exists_subset_card_eq (s := Bᶜ) (n := 14)
    (by rw [card_compl, Fintype.card_fin]; omega)
  exact hasIncidenceIdentity_of_disjoint_zeroSet u (by norm_num) B S hB
    (disjoint_left.2 fun i hi => mem_compl.1 (hS hi))
    (hasIncidenceIdentity_of_card_eq_fourteen (by rw [Fintype.card_coe, hS14]) _)

/-- A zero set with at least fifteen positions gives an integral `𝓘_2`-identity: fourteen of its
positions have an `𝓘_1`-identity (Lemma 5.3(1)), and Lemma 2.2(3) applies. -/
theorem CubeFour.hasIncidenceIdentity_of_fifteen_le_card {v : Fin 18 → (Fin 3 → ZMod 4)}
    {Z : Finset (Fin 18)} (hZ : IsZeroSet v Z) (hcard : 15 ≤ #Z) : HasIncidenceIdentity ℤ v 2 := by
  obtain ⟨T, hTZ, hT14⟩ := exists_subset_card_eq (s := Z) (n := 14) (by omega)
  have hT : T ⊂ Z := ssubset_of_subset_of_ne hTZ fun h => by rw [h] at hT14; omega
  exact hasIncidenceIdentity_of_ssubset_zeroSet v (by norm_num) Z T hZ hT
    (hasIncidenceIdentity_of_card_eq_fourteen (by rw [Fintype.card_coe, hT14]) _)

/-- **Lemma 5.3, Section 5.3, second eighteen-term reduction**: three disjoint zero
sets give the quadratic identity directly by Lemma 2.2(1). -/
theorem CubeFour.hasIncidenceIdentity_two_of_three_disjoint
    (u : Fin 18 → (Fin 3 → ZMod 4)) (B : Fin 3 → Finset (Fin 18))
    (hB : ∀ i, IsZeroSet u (B i)) (hd : Pairwise (Function.onFun Disjoint B)) :
    HasIncidenceIdentity ℤ u 2 :=
  hasIncidenceIdentity_of_pairwise_disjoint u 2 B hB hd

/-- **Lemma 5.3(2), Section 5.3**: every eighteen-term sequence over `C_4^3` has an
integral `𝓘_2`-identity. The three ordinary reductions precede the finite enumeration. -/
theorem hasIncidenceIdentity_cube_four_eighteen (u : Fin 18 → (Fin 3 → ZMod 4)) :
    HasIncidenceIdentity ℤ u 2 := by
  -- First, a short zero set leaves fourteen terms: Lemma 2.2(2).
  by_cases hs : ∃ B, IsZeroSet u B ∧ #B ≤ 4
  · obtain ⟨B, hB, hcard⟩ := hs
    exact hasIncidenceIdentity_two_of_card_le_four hB hcard
  -- Second, three disjoint zero sets give the inclusion–exclusion identity.
  by_cases hd : ∃ B : Fin 3 → Finset (Fin 18),
      (∀ i, IsZeroSet u (B i)) ∧ Pairwise (Function.onFun Disjoint B)
  · obtain ⟨B, hB, hdisj⟩ := hd
    exact hasIncidenceIdentity_two_of_three_disjoint u B hB hdisj
  -- Third, a zero set of at least fifteen positions contains a proper fourteen-term
  -- subsequence; its affine identity lifts by the complement construction, Lemma 2.2(3).
  by_cases hl : ∃ Z, IsZeroSet u Z ∧ 15 ≤ #Z
  · obtain ⟨Z, hZ, hcard⟩ := hl
    exact hasIncidenceIdentity_of_fifteen_le_card hZ hcard
  -- Only the remaining short-zero-free cases reach the unchanged normalized enumeration.
  have hu : ∀ E, IsZeroSet u E → 4 < #E := fun E hE => not_le.1 fun h => hs ⟨E, hE, h⟩
  obtain ⟨φ, hφ, σ, c, hdec, hsort, hlt, hszf, hg, hn3⟩ := exists_sortedCodes u hu
  have hleaf := leaf_of_prefixes leaf18 4 (List.ofFn c) (by simp) hsort hlt hszf hg Checks.top
    (by simpa using Checks.chunks18)
  simp only [leaf18, hn3, Bool.not_true, Bool.false_or, List.reverse_reverse,
    Bool.or_eq_true] at hleaf
  refine hasIncidenceIdentity_of_sortedCodes hφ hdec ?_
  rcases hleaf with h | h
  · -- The checker retains its long-zero alternative as redundant coverage.
    obtain ⟨hZ, hcard⟩ := longZero_sound c h
    exact hasIncidenceIdentity_of_fifteen_le_card hZ hcard
  · exact hasIncidenceIdentity_of_check c _ h

end DavenportProject
