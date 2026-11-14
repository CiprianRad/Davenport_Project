/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Defs
import DavenportProject.Bases.Basic
import DavenportProject.Identities.Operations
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Theorem B for `m = 2`

`hasIncidenceIdentity_cube_two`: every sequence of `2t + 4` terms over `C_2^3` has an integral
`𝓘_t`-identity. Degree one uses the Fano plane construction (`hasIncidenceIdentity_fano`); higher
degrees use `η(C_2^3) ≤ 8` and Lemma 2.2(2).
-/

public section

namespace DavenportProject.Bases

open Finset

/-!
## Short zero sets over `C_2^3`

A sequence over `C_2^3` with a zero or a repeated term has a zero set of size at most two;
every sequence of at least eight terms has a zero or a repetition. In
particular `η(C_2^3) ≤ 8`.
-/

theorem cube_two_add_self (x : Fin 3 → ZMod 2) : x + x = 0 := by
  funext k
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x k = a
  revert a
  decide

/-- A sequence over `C_2^3` that is not injective, or has a zero term, has a zero set of size
at most two. -/
theorem exists_isZeroSet_card_le_two {ι : Type*} (u : ι → (Fin 3 → ZMod 2))
    (h : ¬ (Function.Injective u ∧ ∀ i, u i ≠ 0)) : ∃ B, IsZeroSet u B ∧ #B ≤ 2 := by
  classical
  by_cases h0 : ∃ i, u i = 0
  · obtain ⟨i, hi⟩ := h0
    exact ⟨{i}, ⟨singleton_nonempty i, by simpa using hi⟩, by simp⟩
  · push Not at h0
    have hinj : ¬ Function.Injective u := fun hinj => h ⟨hinj, h0⟩
    simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    refine ⟨{i, j}, ⟨insert_nonempty i _, ?_⟩, card_le_two⟩
    rw [sum_pair hne, hij, cube_two_add_self]

theorem card_ne_zero_cube_two : Fintype.card {x : Fin 3 → ZMod 2 // x ≠ 0} = 7 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  simp

/-- **Section 5.1**, the bound `η(C₂³) ≤ 8`: eight terms cannot be distinct and nonzero. -/
theorem not_injective_and_ne_zero_of_le_card {ι : Type*} [Fintype ι]
    (u : ι → (Fin 3 → ZMod 2)) (h : 8 ≤ Fintype.card ι) :
    ¬ (Function.Injective u ∧ ∀ i, u i ≠ 0) := by
  rintro ⟨hinj, hne⟩
  have := Fintype.card_le_of_injective (fun i => (⟨u i, hne i⟩ : {x : Fin 3 → ZMod 2 // x ≠ 0}))
    (fun i j hij => hinj (congrArg Subtype.val hij))
  rw [card_ne_zero_cube_two] at this
  omega

/-!
## The Fano configuration

Six distinct nonzero terms of `C_2^3` are the Fano plane with one point `x` removed. Weight `1`
on the four lines not through `x` (zero triples) and `-1` on the complements of the three lines
through `x` (zero quadruples) is an integral `𝓘_1`-identity. These are exactly the zero sets of
sizes three and four, so the weight is `fanoW E = [#E = 3] - [#E = 4]`.

For each of the seven choices of `x` we fix an enumeration `fanoSeq x` of the six remaining
points. Kernel checks give the four/three set counts and two/two point incidences;
the identity follows by subtracting these counts. An arbitrary injective nonzero sequence is a
reindexing of `fanoSeq x`, and `hasIncidenceIdentity_comp_equiv` transports the identity.
-/

/-- The seven nonzero points of `C_2^3`. -/
private def fanoPoints : List (Fin 3 → ZMod 2) :=
  [![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

/-- An enumeration of the nonzero points of `C_2^3` other than `x`. -/
private def fanoSeq (x : Fin 3 → ZMod 2) (k : Fin 6) : Fin 3 → ZMod 2 :=
  (fanoPoints.filter (· ≠ x)).getD k 0

/-- The weights of the Fano construction: `1` on triples, `-1` on quadruples. -/
private def fanoW (E : Finset (Fin 6)) : ℤ :=
  if #E = 3 then 1 else if #E = 4 then -1 else 0

/-- Every nonzero point other than `x` occurs in `fanoSeq x`. -/
private theorem fanoSeq_surj : ∀ x : Fin 3 → ZMod 2, x ≠ 0 → ∀ y : Fin 3 → ZMod 2,
    y ≠ 0 → y ≠ x → ∃ k, fanoSeq x k = y := by
  decide +kernel

/-- The zero sets of the six-point Fano configuration. -/
private def fanoZeros (x : Fin 3 → ZMod 2) : Finset (Finset (Fin 6)) :=
  univ.filter fun E => E.Nonempty ∧ ∑ i ∈ E, fanoSeq x i = 0

/-- **Section 5.1, Fano incidence counts**: four selected lines, three complementary
quadruples, and two of each through each remaining point. These are only small geometry checks. -/
private theorem fano_counts : ∀ x : Fin 3 → ZMod 2, x ≠ 0 →
    ((fanoZeros x).filter (fun E => #E = 3)).card = 4 ∧
    ((fanoZeros x).filter (fun E => #E = 4)).card = 3 ∧
    ∀ j : Fin 6,
      (((fanoZeros x).filter (fun E => j ∈ E)).filter (fun E => #E = 3)).card = 2 ∧
      (((fanoZeros x).filter (fun E => j ∈ E)).filter (fun E => #E = 4)).card = 2 := by
  decide +kernel

/-- Sum the paper's weights as the number of selected lines minus complementary quadruples. -/
private theorem sum_fanoW (S : Finset (Finset (Fin 6))) :
    ∑ E ∈ S, fanoW E =
      ((S.filter (fun E => #E = 3)).card : ℤ) - ((S.filter (fun E => #E = 4)).card : ℤ) := by
  have hw (E : Finset (Fin 6)) : fanoW E =
      (if #E = 3 then (1 : ℤ) else 0) - (if #E = 4 then 1 else 0) := by
    unfold fanoW
    split_ifs <;> norm_num
    omega
  simp_rw [hw]
  rw [sum_sub_distrib, sum_boole, sum_boole]

/-- **Section 5.1, Fano identity**: the total weight is `4 - 3 = 1` and every
point moment is `2 - 2 = 0`, as counted in the paper. -/
private theorem hasIncidenceIdentity_fanoSeq (x : Fin 3 → ZMod 2) (hx : x ≠ 0) :
    HasIncidenceIdentity ℤ (fanoSeq x) 1 := by
  classical
  have hZ : zeroSets (fanoSeq x) = fanoZeros x := by
    ext E
    simp [fanoZeros, mem_zeroSets, IsZeroSet]
  obtain ⟨h3, h4, hthrough⟩ := fano_counts x hx
  refine ⟨fanoW, ?_, ?_⟩
  · -- The four line weights and three negative quadruple weights total one.
    rw [hZ, sum_fanoW, h3, h4]
    norm_num
  · -- Through each remaining point, two positive and two negative weights cancel.
    intro J hJ1 hJ2
    obtain ⟨j, rfl⟩ := card_eq_one.1 (le_antisymm hJ2 hJ1)
    simp only [hZ, singleton_subset_iff]
    rw [sum_fanoW, (hthrough j).1, (hthrough j).2]
    norm_num

/-- **Section 5.1, Fano construction**: six distinct nonzero terms of `C_2^3`
(the Fano plane minus a point) have an integral `𝓘_1`-identity. -/
theorem hasIncidenceIdentity_fano (u : Fin 6 → (Fin 3 → ZMod 2)) (hinj : Function.Injective u)
    (hne : ∀ i, u i ≠ 0) :
    HasIncidenceIdentity ℤ u 1 := by
  classical
  -- the removed point `x`
  obtain ⟨x, hx⟩ : (univ \ insert 0 (univ.image u)).Nonempty := by
    have h0 : (0 : Fin 3 → ZMod 2) ∉ univ.image u := by simpa using fun i => hne i
    rw [← card_pos, card_sdiff_of_subset (subset_univ _), card_insert_of_notMem h0,
      card_image_of_injective _ hinj]
    simp
  simp only [mem_sdiff, mem_univ, mem_insert, mem_image, true_and, not_or, not_exists] at hx
  obtain ⟨hx0, hxu⟩ := hx
  -- `u` is a reindexing of `fanoSeq x`
  choose σ hσ using fun i => fanoSeq_surj x hx0 (u i) (hne i) (fun h => hxu i h)
  have hσinj : Function.Injective σ := fun i j h => hinj (by rw [← hσ i, ← hσ j, h])
  let e : Fin 6 ≃ Fin 6 := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσinj)
  have hu : u = fun i => fanoSeq x (e i) := funext fun i => (hσ i).symm
  rw [hu]
  exact hasIncidenceIdentity_comp_equiv _ e (hasIncidenceIdentity_fanoSeq x hx0)

/-!
## Proof of Theorem B for `m = 2`

Every sequence of `2t + 4` terms over `C_2^3` has an integral `𝓘_t`-identity, by induction on
`t` over an arbitrary index type of that cardinality:
* `t = 0`: a zero set exists since `D(C_2^3) = 4`; apply Lemma 2.2(1).
* `t = 1`, with a zero set of at most two positions: the remaining four terms supply a
  second disjoint zero set, so Lemma 2.2(1) applies.
* `t ≥ 2`, with a short zero set: the remainder has the preceding-degree identity;
  apply the short-zero recurrence of Lemma 2.2(2).
* otherwise the terms are distinct and nonzero, so there are at most seven of them; hence
  `t = 1`, the six terms form the Fano configuration, and `hasIncidenceIdentity_fano` applies.
-/

/-- Degree zero: four terms over `C_2^3` have an integral `𝓘_0`-identity (`D(C_2^3) = 4`). -/
theorem hasIncidenceIdentity_zero_of_card_eq_four {ι : Type*} [Fintype ι]
    (h : Fintype.card ι = 4) (u : ι → (Fin 3 → ZMod 2)) : HasIncidenceIdentity ℤ u 0 := by
  let e : ι ≃ Fin 4 := Fintype.equivFinOfCardEq h
  obtain ⟨E, hE⟩ :=
    ((davenport_eq_iff _ 4).1 davenport_cube_two).1 (fun k => u (e.symm k))
  have hB : IsZeroSet u (E.map e.symm.toEmbedding) := (isZeroSet_map_equiv u e.symm E).2 hE
  exact hasIncidenceIdentity_of_pairwise_disjoint u 0 (fun _ => E.map e.symm.toEmbedding)
    (fun _ => hB) (fun i j hij => absurd (Subsingleton.elim (α := Fin 1) i j) hij)

/-- **Theorem B for `m = 2`, Section 5.1**, over an arbitrary index type with `2t + 4` positions. -/
theorem hasIncidenceIdentity_cube_two_of_card (t : ℕ) :
    ∀ (ι : Type) [Fintype ι], Fintype.card ι = 2 * t + 4 →
      ∀ u : ι → (Fin 3 → ZMod 2), HasIncidenceIdentity ℤ u t := by
  induction t with
  | zero =>
    intro ι _ h u
    exact hasIncidenceIdentity_zero_of_card_eq_four h u
  | succ t ih =>
    intro ι _ h u
    classical
    by_cases hgen : Function.Injective u ∧ ∀ i, u i ≠ 0
    · -- distinct nonzero terms: only possible for `t + 1 = 1`, the Fano configuration
      have ht : t = 0 := by
        by_contra ht
        exact not_injective_and_ne_zero_of_le_card u (by omega) hgen
      subst ht
      let e : ι ≃ Fin 6 := Fintype.equivFinOfCardEq h
      have hF := hasIncidenceIdentity_fano (fun k => u (e.symm k))
        (fun i j hij => e.symm.injective (hgen.1 hij)) (fun k => hgen.2 _)
      have := hasIncidenceIdentity_comp_equiv _ e hF
      simpa using this
    · -- a zero set `B` of size at most two; Lemma 2.2(2)
      obtain ⟨B, hB, hBcard⟩ := exists_isZeroSet_card_le_two u hgen
      have hc : 2 * t + 4 ≤ #Bᶜ := by
        rw [card_compl]
        omega
      obtain ⟨S, hS, hScard⟩ := exists_subset_card_eq hc
      have hSB : Disjoint S B := disjoint_left.2 fun i hi => mem_compl.1 (hS hi)
      by_cases ht : t = 0
      · -- Degree one: the four remaining terms give a second zero set; use Lemma 2.2(1).
        subst t
        let e : S ≃ Fin 4 := Fintype.equivFinOfCardEq (by simpa using hScard)
        let f : Fin 4 ↪ ι := e.symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ S))
        obtain ⟨F', hF'⟩ := ((davenport_eq_iff _ 4).1 davenport_cube_two).1 (fun k => u (f k))
        let F := F'.map f
        have hF : IsZeroSet u F := by
          refine ⟨hF'.1.map, ?_⟩
          rw [sum_map]
          exact hF'.2
        have hBF : Disjoint B F := by
          rw [disjoint_iff_ne]
          rintro a ha b hb rfl
          obtain ⟨i, -, rfl⟩ := mem_map.1 hb
          exact (disjoint_left.1 hSB (e.symm i).2) ha
        refine hasIncidenceIdentity_of_pairwise_disjoint u 1 ![B, F] ?_ ?_
        · intro k
          fin_cases k
          exacts [hB, hF]
        · intro i j hij
          fin_cases i <;> fin_cases j
          · exact absurd rfl hij
          · exact hBF
          · exact hBF.symm
          · exact absurd rfl hij
      · -- Higher degrees: the short-zero recurrence is Lemma 2.2(2).
        exact hasIncidenceIdentity_of_disjoint_zeroSet u (Nat.le_add_left 1 t) B S hB hSB
          (ih S (by rw [Fintype.card_coe, hScard]) _)

/-- Theorem B for `m = 2`: every sequence of `2(t+3) - 2` terms over
`C_2^3` has an integral `𝓘_t`-identity. -/
theorem hasIncidenceIdentity_cube_two (t : ℕ) (u : Fin (2 * (t + 3) - 2) → (Fin 3 → ZMod 2)) :
    HasIncidenceIdentity ℤ u t :=
  hasIncidenceIdentity_cube_two_of_card t _ (by rw [Fintype.card_fin]; omega) u

end DavenportProject.Bases
