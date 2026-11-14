/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Invariants
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.MvPolynomial.Basic
import DavenportProject.Transfer.Augmentation
import Mathlib.Algebra.Field.ZMod

/-!
# Olson's theorem

`davenport_pi_zmod_prime_pow`: for a prime `p`, `D(⊕ᵢ C_{p^{aᵢ}}) = 1 + ∑ᵢ (p^{aᵢ} - 1)`
(Olson 1969). Write `H = ∏ᵢ ZMod (p ^ aᵢ)` and `M = ∑ᵢ (p ^ aᵢ - 1)`.
* Upper bound, from the nilpotency of the augmentation ideal: for `u : Fin (M + 1) → H`, the
  product `∏ⱼ (X^{uⱼ} - 1)` vanishes in `𝔽_p[H]`. Expanding it over subsets, its coefficient at
  `0` is `±1` if `∅` is the only zero-sum subset.
* Lower bound: `p ^ aᵢ - 1` copies of each basis vector `eᵢ` form a zero-sum free sequence of
  length `M`; its initial segments are zero-sum free as well.
-/

public section

namespace DavenportProject

open Finset Transfer

namespace Transfer

variable {p : ℕ} [Fact p.Prime] {r : ℕ} {a : Fin r → ℕ}

/-- Every sequence of length `M + 1` in `∏ᵢ ZMod (p ^ aᵢ)` has a zero set. -/
theorem exists_isZeroSet (u : Fin (∑ i, (p ^ a i - 1) + 1) → (i : Fin r) → ZMod (p ^ a i)) :
    ∃ E, IsZeroSet u E := by
  classical
  by_contra hne
  push Not at hne
  have h0 : ∏ j ∈ (univ : Finset (Fin (∑ i, (p ^ a i - 1) + 1))),
      (AddMonoidAlgebra.single (u j) (1 : ZMod p) - 1) = 0 :=
    Transfer.prod_single_sub_one_eq_zero (a := a) univ u (by simp)
  have hexp : ∀ j, AddMonoidAlgebra.single (u j) (1 : ZMod p) - 1 =
      AddMonoidAlgebra.single (u j) 1 + AddMonoidAlgebra.single 0 (-1) := by
    intro j
    rw [AddMonoidAlgebra.single_neg, ← AddMonoidAlgebra.one_def, sub_eq_add_neg]
  simp_rw [hexp] at h0
  rw [prod_add] at h0
  simp_rw [AddMonoidAlgebra.prod_single, AddMonoidAlgebra.single_mul_single] at h0
  have hc := congrArg (fun x => AddMonoidAlgebra.coeff x 0) h0
  simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, sum_const_zero,
    AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, Finset.sum_apply',
    Finsupp.single_apply, add_zero] at hc
  rw [sum_eq_single (∅ : Finset _)] at hc
  · simp at hc
  · intro t _ ht
    have hsum : ¬ ∑ i ∈ t, u i = 0 := fun hsum => hne t ⟨nonempty_iff_ne_empty.mpr ht, hsum⟩
    simp [hsum]
  · simp

/-- The index type of the basis sequence: `p ^ aᵢ - 1` slots for each coordinate `i`. -/
abbrev BasisIdx (p : ℕ) (a : Fin r → ℕ) : Type := (i : Fin r) × Fin (p ^ a i - 1)

/-- The basis sequence: slot `⟨i, k⟩` carries the basis vector `eᵢ`. -/
noncomputable def basisSeq (p : ℕ) (a : Fin r → ℕ) (x : BasisIdx p a) :
    (i : Fin r) → ZMod (p ^ a i) :=
  Pi.single x.1 1

omit [Fact p.Prime] in
theorem card_basisIdx : Fintype.card (BasisIdx p a) = ∑ i, (p ^ a i - 1) := by
  simp

/-- The basis sequence is zero-sum free. -/
theorem not_isZeroSet_basisSeq (E : Finset (BasisIdx p a)) : ¬ IsZeroSet (basisSeq p a) E := by
  classical
  rintro ⟨⟨x, hx⟩, hsum⟩
  set i := x.1
  have hi := congrFun hsum i
  simp only [basisSeq, Finset.sum_apply, Pi.zero_apply] at hi
  have hterm : ∀ y ∈ E, (Pi.single y.1 1 : (i : Fin r) → ZMod (p ^ a i)) i =
      if i = y.1 then 1 else 0 := by
    rintro ⟨j, k⟩ -
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  rw [sum_congr rfl hterm] at hi
  rw [sum_boole, ZMod.natCast_eq_zero_iff] at hi
  have hpos : 0 < #{y ∈ E | i = y.1} := card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩
  have hle : #{y ∈ E | i = y.1} ≤ #(range (p ^ a i - 1)) := by
    refine card_le_card_of_injOn (fun y => (y.2 : ℕ)) ?_ ?_
    · intro y hy
      have hy' := (mem_filter.mp hy).2
      simp only [coe_range, Set.mem_Iio]
      have h1 := y.2.2
      have h2 : p ^ a i = p ^ a y.1 := by rw [hy']
      omega
    · intro y hy z hz hyz
      obtain ⟨yi, yk⟩ := y
      obtain ⟨zi, zk⟩ := z
      have hy' := (mem_filter.mp hy).2
      have hz' := (mem_filter.mp hz).2
      simp only at hy' hz' hyz
      subst hy' hz'
      simp [Fin.ext hyz]
  rw [card_range] at hle
  have := Nat.le_of_dvd hpos hi
  have hp : 0 < p ^ a i := pow_pos (Fact.out : p.Prime).pos _
  omega

/-- For every `L' < M + 1` there is a zero-sum free sequence of length `L'`. -/
theorem exists_not_isZeroSet {L' : ℕ} (hL : L' < ∑ i, (p ^ a i - 1) + 1) :
    ∃ u : Fin L' → (i : Fin r) → ZMod (p ^ a i), ∀ E, ¬ IsZeroSet u E := by
  classical
  let e : Fin L' ↪ BasisIdx p a :=
    (Fin.castLEEmb (by rw [card_basisIdx]; omega)).trans
      (Fintype.equivFinOfCardEq rfl).symm.toEmbedding
  refine ⟨basisSeq p a ∘ e, fun E hE => not_isZeroSet_basisSeq (E.map e) ?_⟩
  obtain ⟨hne, hsum⟩ := hE
  exact ⟨hne.map, by rw [sum_map]; exact hsum⟩

end Transfer

/-- Olson's theorem (Olson 1969):
`D(⊕_i C_{p^{a_i}}) = 1 + ∑_i (p^{a_i} - 1)`. -/
theorem davenport_pi_zmod_prime_pow (p : ℕ) [Fact p.Prime] {r : ℕ} (a : Fin r → ℕ) :
    davenport ((i : Fin r) → ZMod (p ^ a i)) = 1 + ∑ i, (p ^ a i - 1) := by
  rw [add_comm, davenport_eq_iff]
  exact ⟨exists_isZeroSet, fun _ hL => exists_not_isZeroSet hL⟩

end DavenportProject
