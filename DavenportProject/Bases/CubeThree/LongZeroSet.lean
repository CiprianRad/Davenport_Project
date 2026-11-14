/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Defs
public import Mathlib.Data.ZMod.Basic
import DavenportProject.Bases.CubeThree.Support
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Lemma 5.2

`exists_large_zeroSet_cube_three`: every short-zero-free sequence of thirteen terms over `C_3^3`
has a zero set of size at least eleven.
-/

public section

namespace DavenportProject

open Finset CubeThree

/-!
## Allowed supports in `C_3^3`

A finite set `A ⊆ C_3^3` is *allowed* if it contains no zero, no two
distinct points with sum zero and no three distinct points with sum zero. Through
Lemma 5.1(2) (`card_support_le_of_isShortZeroFree_cube_three`), an allowed set has at most eight
points, a seven-point allowed set has nonzero sum and an eight-point allowed set sums to zero
(`allowed_spec`). An inclusion-maximal allowed set represents every point as a sum of at most
two terms of `2A` (`rep_of_maximal`).
-/

namespace CubeThree

theorem add_self_add_self (x : Fin 3 → ZMod 3) : x + x + x = 0 := by
  funext k
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x k = a
  revert a
  decide

theorem neg_eq_add_self (x : Fin 3 → ZMod 3) : -x = x + x := by
  rw [neg_eq_iff_add_eq_zero, ← add_assoc]
  exact add_self_add_self x

theorem eq_zero_of_add_self_eq_zero {x : Fin 3 → ZMod 3} (h : x + x = 0) : x = 0 := by
  have := add_self_add_self x
  rwa [h, zero_add] at this

theorem exponent_eq_three : AddMonoid.exponent (Fin 3 → ZMod 3) = 3 := by
  apply le_antisymm
  · refine Nat.le_of_dvd (by norm_num)
      (AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero fun x => ?_)
    rw [show 3 • x = 2 • x + x from succ_nsmul x 2, two_nsmul]
    exact add_self_add_self x
  · have hne : AddMonoid.exponent (Fin 3 → ZMod 3) ≠ 0 := AddMonoid.exponent_ne_zero_of_finite
    have h := congrFun (AddMonoid.exponent_nsmul_eq_zero (fun _ : Fin 3 => (1 : ZMod 3))) 0
    simp only [Pi.smul_apply, nsmul_eq_mul, mul_one, Pi.zero_apply,
      ZMod.natCast_eq_zero_iff] at h
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h

/-- An *allowed* support: no zero, no two distinct points with sum zero
and no three distinct points with sum zero. -/
@[expose] def Allowed (A : Finset (Fin 3 → ZMod 3)) : Prop :=
  0 ∉ A ∧ (∀ x ∈ A, ∀ y ∈ A, x ≠ y → x + y ≠ 0) ∧
    ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → x ≠ z → y ≠ z → x + y + z ≠ 0

/-- The points of `A`, listed without repetition. -/
@[expose] noncomputable def listing (A : Finset (Fin 3 → ZMod 3)) (i : Fin #A) : Fin 3 → ZMod 3 :=
  (A.equivFin.symm i : Fin 3 → ZMod 3)

theorem image_listing (A : Finset (Fin 3 → ZMod 3)) : univ.image (listing A) = A := by
  ext x
  simp only [mem_image, mem_univ, true_and, listing]
  constructor
  · rintro ⟨i, rfl⟩
    exact (A.equivFin.symm i).2
  · intro hx
    exact ⟨A.equivFin ⟨x, hx⟩, by simp⟩

theorem isShortZeroFree_listing {A : Finset (Fin 3 → ZMod 3)} (hA : Allowed A) :
    IsShortZeroFree (listing A) := by
  rintro E ⟨hne, hs⟩
  rw [exponent_eq_three]
  by_contra hle
  have hinj : Function.Injective (listing A) := fun i j h =>
    A.equivFin.symm.injective (Subtype.ext h)
  have hmem : ∀ i, listing A i ∈ A := fun i => (A.equivFin.symm i).2
  obtain ⟨h0, h2, h3⟩ := hA
  have hc : #E = 1 ∨ #E = 2 ∨ #E = 3 := by
    have := hne.card_pos
    omega
  rcases hc with hc | hc | hc
  · obtain ⟨i, rfl⟩ := card_eq_one.1 hc
    rw [sum_singleton] at hs
    exact h0 (hs ▸ hmem i)
  · obtain ⟨i, j, hij, rfl⟩ := card_eq_two.1 hc
    rw [sum_pair hij] at hs
    exact h2 _ (hmem i) _ (hmem j) (hinj.ne hij) hs
  · obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := card_eq_three.1 hc
    rw [sum_insert (by simp [hij, hik]), sum_pair hjk, ← add_assoc] at hs
    exact h3 _ (hmem i) _ (hmem j) _ (hmem k) (hinj.ne hij) (hinj.ne hik) (hinj.ne hjk) hs

/-- Lemma 5.1(2) for allowed sets. -/
theorem allowed_spec {A : Finset (Fin 3 → ZMod 3)} (hA : Allowed A) :
    #A ≤ 8 ∧ (#A = 7 → ∑ x ∈ A, x ≠ 0) ∧ (#A = 8 → ∑ x ∈ A, x = 0) := by
  have := card_support_le_of_isShortZeroFree_cube_three _ (isShortZeroFree_listing hA)
  rwa [image_listing] at this

theorem eq_add_of_neg_add_add {x a b : Fin 3 → ZMod 3} (h : -x + a + b = 0) : x = a + b := by
  rw [← sub_eq_zero, ← neg_eq_zero, ← h]
  abel

/-- an inclusion-maximal allowed set `A` represents every point `x` as a
sum of at most two terms of `2A`: `x = 0`, `x ∈ A`, `x = (-x) + (-x)` with `-x ∈ A`, or
`x = a + b` with distinct `a, b ∈ A`. -/
theorem rep_of_maximal {A : Finset (Fin 3 → ZMod 3)} (hA : Allowed A)
    (hmax : ∀ y ∉ A, ¬ Allowed (insert y A)) (x : Fin 3 → ZMod 3) :
    x = 0 ∨ x ∈ A ∨ -x ∈ A ∨ ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ x = a + b := by
  by_contra! h
  obtain ⟨hx0, hxA, hnxA, hab⟩ := h
  obtain ⟨h0, h2, h3⟩ := hA
  refine hmax (-x) hnxA ⟨?_, ?_, ?_⟩
  · rw [mem_insert, not_or]
    exact ⟨fun e => hx0 (neg_eq_zero.1 e.symm), h0⟩
  · intro a ha b hb hne e
    rw [mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact hne rfl
    · exact hxA (neg_add_eq_zero.1 e ▸ hb)
    · exact hxA ((add_neg_eq_zero.1 e) ▸ ha)
    · exact h2 a ha b hb hne e
  · intro a ha b hb c hc hab' hac hbc e
    rw [mem_insert] at ha hb hc
    rcases ha with rfl | ha <;> rcases hb with rfl | hb <;> rcases hc with rfl | hc
    · exact hab' rfl
    · exact hab' rfl
    · exact hac rfl
    · exact hab _ hb _ hc hbc (eq_add_of_neg_add_add e)
    · exact hbc rfl
    · exact hab _ ha _ hc hac (eq_add_of_neg_add_add (by rw [← e]; abel))
    · exact hab _ ha _ hb hab' (eq_add_of_neg_add_add (by rw [← e]; abel))
    · exact h3 a ha b hb c hc hab' hac hbc e

section Sequence

variable {N : ℕ} {u : Fin N → (Fin 3 → ZMod 3)}

/-- A short-zero-free sequence over `C_3^3` has no zero set of size at most three. -/
theorem sum_ne_zero_of_card_le_three (hu : IsShortZeroFree u) {E : Finset (Fin N)}
    (hE : E.Nonempty) (hc : #E ≤ 3) : ∑ i ∈ E, u i ≠ 0 :=
  fun hs => absurd (hu E ⟨hE, hs⟩) (by rw [exponent_eq_three]; omega)

/-- The support of a short-zero-free sequence over `C_3^3` is allowed. -/
theorem allowed_image (hu : IsShortZeroFree u) : Allowed (univ.image u) := by
  have hA : ∀ x ∈ univ.image u, ∃ i, u i = x := fun x hx => by simpa using hx
  refine ⟨fun h0 => ?_, fun x hx y hy hxy hs => ?_, fun x hx y hy z hz hxy hxz hyz hs => ?_⟩
  · obtain ⟨i, hi⟩ := hA 0 h0
    exact sum_ne_zero_of_card_le_three hu (singleton_nonempty i) (by simp) (by simpa using hi)
  · obtain ⟨i, rfl⟩ := hA x hx
    obtain ⟨j, rfl⟩ := hA y hy
    have hij : i ≠ j := fun e => hxy (by rw [e])
    exact sum_ne_zero_of_card_le_three hu (insert_nonempty i _)
      (card_le_two.trans (by norm_num)) (by rwa [sum_pair hij])
  · obtain ⟨i, rfl⟩ := hA x hx
    obtain ⟨j, rfl⟩ := hA y hy
    obtain ⟨k, rfl⟩ := hA z hz
    have hij : i ≠ j := fun e => hxy (by rw [e])
    have hik : i ≠ k := fun e => hxz (by rw [e])
    have hjk : j ≠ k := fun e => hyz (by rw [e])
    refine sum_ne_zero_of_card_le_three hu (E := {i, j, k}) (insert_nonempty i _) card_le_three ?_
    rwa [sum_insert (by simp [hij, hik]), sum_pair hjk, ← add_assoc]

/-- Every point occurs at most twice in a short-zero-free sequence over `C_3^3`
(three equal terms sum to zero). -/
theorem card_filter_le_two (hu : IsShortZeroFree u) (x : Fin 3 → ZMod 3) :
    #{i | u i = x} ≤ 2 := by
  by_contra h
  obtain ⟨E, hE, hc⟩ := exists_subset_card_eq (show 3 ≤ #{i | u i = x} by omega)
  refine sum_ne_zero_of_card_le_three hu (card_pos.1 (by omega)) hc.le ?_
  rw [sum_congr rfl fun i hi => (mem_filter.1 (hE hi)).2, sum_const, hc,
    show 3 • x = 2 • x + x from succ_nsmul x 2, two_nsmul]
  exact add_self_add_self x

/-- `x` is a sum of at most two terms of `u` at distinct positions. -/
def IsRep (u : Fin N → (Fin 3 → ZMod 3)) (x : Fin 3 → ZMod 3) : Prop :=
  ∃ F : Finset (Fin N), #F ≤ 2 ∧ ∑ i ∈ F, u i = x

theorem isRep_zero : IsRep u 0 := ⟨∅, by simp, by simp⟩

theorem isRep_of_mem {x : Fin 3 → ZMod 3} (hx : x ∈ univ.image u) : IsRep u x := by
  obtain ⟨i, -, rfl⟩ := mem_image.1 hx
  exact ⟨{i}, by simp, by simp⟩

theorem isRep_add {x y : Fin 3 → ZMod 3} (hx : x ∈ univ.image u) (hy : y ∈ univ.image u)
    (hxy : x ≠ y) : IsRep u (x + y) := by
  obtain ⟨i, -, rfl⟩ := mem_image.1 hx
  obtain ⟨j, -, rfl⟩ := mem_image.1 hy
  have hij : i ≠ j := fun e => hxy (by rw [e])
  exact ⟨{i, j}, card_le_two, sum_pair hij⟩

theorem isRep_add_self {x : Fin 3 → ZMod 3} (hx : 2 ≤ #{i | u i = x}) : IsRep u (x + x) := by
  obtain ⟨E, hE, hc⟩ := exists_subset_card_eq hx
  obtain ⟨i, j, hij, rfl⟩ := card_eq_two.1 hc
  refine ⟨{i, j}, card_le_two, ?_⟩
  rw [sum_pair hij, (mem_filter.1 (hE (mem_insert_self i _))).2,
    (mem_filter.1 (hE (mem_insert_of_mem (mem_singleton_self j)))).2]

end Sequence

/-!
## Proof of Lemma 5.2

Let `U` be short-zero-free of length thirteen with support
`A` and total sum `σ`. Every point occurs at most twice, and `A` is allowed, so by
Lemma 5.1(2) (through `allowed_spec`) `A` has seven or eight points. It suffices to write `σ` as
the sum of at most two terms of `U` at distinct positions (`exists_rep`): the complement of
these positions is a zero set of size at least eleven.

Writing `S₁ ⊆ A` for the points of multiplicity one, `#S₁ + 13 = 2 #A` and
`σ = 2 σ(A) - σ(S₁)`. A representation of `σ` from `rep_of_maximal` for a maximal allowed set
is available in `U` unless it uses a point of `S₁` twice; the remaining cases contradict the
support conditions or Lemma 5.1(2), exactly as in the paper:

* `#A = 8`: `A` is maximal and `σ = -σ(S₁)`; `-σ ∈ S₁` would leave two points of
  `S₁` with sum zero.
* `#A = 7`, `S₁ = {a₀}`: if `A` is maximal, `-σ = a₀` forces `σ(A) = 0`;
  otherwise `A ∪ {b}` is an allowed (hence maximal) eight-set with `σ(A) = -b`, and each
  unavailable representation forces `a₀ = 0`, `a₀ + b = 0` or `c + a₀ = 0` with `c ∈ A`.
-/

/-- The heart of Lemma 5.2: the total sum of a short-zero-free sequence of thirteen terms over
`C_3^3` is a sum of at most two of its terms. -/
theorem exists_rep {u : Fin 13 → (Fin 3 → ZMod 3)} (hu : IsShortZeroFree u) :
    IsRep u (∑ i, u i) := by
  set σ := ∑ i, u i
  set A := univ.image u
  have hA : Allowed A := allowed_image hu
  obtain ⟨hle8, h7, h8⟩ := allowed_spec hA
  set m : (Fin 3 → ZMod 3) → ℕ := fun x => #{i | u i = x} with hm_def
  have hm2 : ∀ x, m x ≤ 2 := card_filter_le_two hu
  have hm1 : ∀ x ∈ A, 1 ≤ m x := fun x hx => by
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx
    exact card_pos.2 ⟨i, by simp⟩
  set S₁ := A.filter (fun x => m x = 1) with hS₁_def
  have hS₁A : S₁ ⊆ A := filter_subset _ _
  -- multiplicity counts: `#S₁ + 13 = 2 #A`
  have hcard : #S₁ + 13 = 2 * #A := by
    have h13 : (13 : ℕ) = ∑ x ∈ A, m x := by
      have := card_eq_sum_card_image u univ
      rwa [card_univ, Fintype.card_fin] at this
    rw [h13, hS₁_def, card_filter, ← sum_add_distrib, mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun x hx => ?_
    have := hm1 x hx
    have := hm2 x
    split_ifs <;> omega
  -- the total sum: `σ = 2 σ(A) - σ(S₁)`
  have hσ : σ = (∑ x ∈ A, x) + (∑ x ∈ A, x) - ∑ x ∈ S₁, x := by
    have h := sum_comp (s := univ) (fun x : Fin 3 → ZMod 3 => x) u
    refine h.trans ?_
    rw [← sum_add_distrib, hS₁_def, sum_filter, ← sum_sub_distrib]
    refine sum_congr rfl fun x hx => ?_
    have := hm1 x hx
    have := hm2 x
    by_cases h1 : m x = 1
    · simp only [h1, ↓reduceIte, add_sub_cancel_right]
      change m x • x = x
      rw [h1, one_smul]
    · simp only [h1, ↓reduceIte, sub_zero, ← two_nsmul]
      change m x • x = 2 • x
      rw [show m x = 2 by omega]
  -- a point of `A` outside `S₁` occurs twice
  have hdouble : ∀ x ∈ A, x ∉ S₁ → IsRep u (x + x) := fun x hx hxS => by
    have := hm1 x hx
    have hx1 : m x ≠ 1 := fun e => hxS (mem_filter.2 ⟨hx, e⟩)
    exact isRep_add_self (show 2 ≤ m x by omega)
  have hneg : ∀ y : Fin 3 → ZMod 3, y = -y + -y := fun y => by
    rw [← neg_eq_add_self, neg_neg]
  -- the representations of `rep_of_maximal` with all terms in `A`
  have good : ∀ (h : -σ ∈ A → -σ ∉ S₁),
      σ = 0 ∨ σ ∈ A ∨ -σ ∈ A ∨ (∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ σ = a + b) → IsRep u σ := by
    rintro hS (h | h | h | ⟨a, ha, b, hb, hab, h⟩)
    · rw [h]; exact isRep_zero
    · exact isRep_of_mem h
    · rw [hneg σ]; exact hdouble _ h (hS h)
    · rw [h]; exact isRep_add ha hb hab
  obtain ⟨h0, h2, -⟩ := id hA
  have hmax8 : ∀ {B : Finset (Fin 3 → ZMod 3)}, #B = 8 → ∀ y ∉ B, ¬ Allowed (insert y B) :=
    fun hB y hy hY => by
      have := (allowed_spec hY).1
      rw [card_insert_of_notMem hy] at this
      omega
  have hA78 : #A = 7 ∨ #A = 8 := by omega
  rcases hA78 with hA7 | hA8
  · -- seven-point support: `U = 2A - a₀`
    obtain ⟨a₀, ha₀⟩ := card_eq_one.1 (show #S₁ = 1 by omega)
    have ha₀A : a₀ ∈ A := hS₁A (ha₀ ▸ mem_singleton_self a₀)
    rw [ha₀, sum_singleton] at hσ
    have hsA := h7 hA7
    have hS : -σ ∈ A → -σ ∉ S₁ := fun _ hS => by
      rw [ha₀, mem_singleton] at hS
      exact hsA (eq_zero_of_add_self_eq_zero (by linear_combination (norm := module) -hσ - hS))
    by_cases hmax : ∀ y ∉ A, ¬ Allowed (insert y A)
    · exact good hS (rep_of_maximal hA hmax σ)
    push Not at hmax
    obtain ⟨b, hb, hB⟩ := hmax
    have hB8 : #(insert b A) = 8 := by rw [card_insert_of_notMem hb, hA7]
    have hsB : b + ∑ x ∈ A, x = 0 := by
      have := (allowed_spec hB).2.2 hB8
      rwa [sum_insert hb] at this
    have ht := add_self_add_self b
    have ha₀b : a₀ ≠ b := fun e => hb (e ▸ ha₀A)
    have ha₀0 : a₀ ≠ 0 := fun e => h0 (e ▸ ha₀A)
    rcases rep_of_maximal hB (hmax8 hB8) σ with h | h | h | ⟨x, hx, y, hy, hxy, h⟩
    · exact good hS (Or.inl h)
    · rcases mem_insert.1 h with h | h
      · exact absurd (by linear_combination (norm := module) hσ + (2 : ℤ) • hsB - h - ht) ha₀0
      · exact good hS (Or.inr (Or.inl h))
    · rcases mem_insert.1 h with h | h
      · refine absurd ?_ (hB.2.1 a₀ (mem_insert_of_mem ha₀A) b (mem_insert_self b A) ha₀b)
        linear_combination (norm := module) hσ + (2 : ℤ) • hsB + h
      · exact good hS (Or.inr (Or.inr (Or.inl h)))
    · -- `c + a₀ = 0` for the second summand `c ∈ A`
      have hc : ∀ c ∈ A, σ ≠ b + c := fun c hc e => by
        have e' : c + a₀ = 0 := by
          linear_combination (norm := module) hσ + (2 : ℤ) • hsB - e - ht
        by_cases hca : c = a₀
        · rw [hca] at e'
          exact ha₀0 (eq_zero_of_add_self_eq_zero e')
        · exact h2 c hc a₀ ha₀A hca e'
      rcases mem_insert.1 hx with hx' | hx' <;> rcases mem_insert.1 hy with hy' | hy'
      · exact absurd (hx'.trans hy'.symm) hxy
      · rw [hx'] at h
        exact absurd h (hc y hy')
      · rw [hy', add_comm] at h
        exact absurd h (hc x hx')
      · exact good hS (Or.inr (Or.inr (Or.inr ⟨x, hx', y, hy', hxy, h⟩)))
  · -- eight-point support: `U = 2B - b - c - d`
    have hS₁3 : #S₁ = 3 := by omega
    rw [h8 hA8, add_zero, zero_sub] at hσ
    have hS : -σ ∈ A → -σ ∉ S₁ := fun _ hS => by
      have hsum : ∑ x ∈ S₁.erase (-σ), x = 0 := by
        rw [sum_erase_eq_sub hS, hσ, neg_neg, sub_self]
      obtain ⟨c, d, hcd, he⟩ := card_eq_two.1 (show #(S₁.erase (-σ)) = 2 by
        rw [card_erase_of_mem hS, hS₁3])
      have hc : c ∈ A := hS₁A (mem_of_mem_erase (he ▸ mem_insert_self c _))
      have hd : d ∈ A := hS₁A (mem_of_mem_erase (he ▸ mem_insert_of_mem (mem_singleton_self d)))
      rw [he, sum_pair hcd] at hsum
      exact h2 c hc d hd hcd hsum
    exact good hS (rep_of_maximal hA (hmax8 hA8) σ)

end CubeThree

/-- **Lemma 5.2, Section 5.2**: every short-zero-free sequence of thirteen terms over
`C_3^3` has a zero set of size at least eleven. -/
theorem exists_large_zeroSet_cube_three (u : Fin 13 → (Fin 3 → ZMod 3))
    (hu : IsShortZeroFree u) :
    ∃ E, IsZeroSet u E ∧ 11 ≤ #E := by
  obtain ⟨F, hF, hsum⟩ := exists_rep hu
  have hcard : 11 ≤ #(univ \ F) := by
    rw [card_sdiff_of_subset (subset_univ F), card_univ, Fintype.card_fin]
    omega
  refine ⟨univ \ F, ⟨card_pos.1 (by omega), ?_⟩, hcard⟩
  rw [← sub_eq_zero.2 hsum.symm, eq_sub_iff_add_eq, sum_sdiff (subset_univ F)]

end DavenportProject
