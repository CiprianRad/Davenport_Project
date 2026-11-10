/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Defs
import DavenportProject.Identities.PolynomialLifting
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination

/-!
# Lemma 2.2: three constructions of identities

* `hasIncidenceIdentity_of_pairwise_disjoint` (Lemma 2.2(1)): `t + 1` pairwise disjoint zero sets.
* `hasIncidenceIdentity_of_disjoint_zeroSet` (Lemma 2.2(2)): a zero set together with an
  `𝓘_{t-1}`-identity on a disjoint subsequence.
* `hasIncidenceIdentity_of_ssubset_zeroSet` (Lemma 2.2(3)): an `𝓘_{t-1}`-identity on a proper
  subsequence of a zero set.
-/

public section

namespace DavenportProject

open Finset

variable {G : Type*} [AddCommGroup G] {ι : Type*}

/-!
## Transport of zero sets between a subsequence and the full sequence

For `S : Finset ι`, the subsequence `fun i : S => u i` has zero sets `E : Finset S`; these
correspond to the zero sets of `u` contained in `S` via `E ↦ E.map (Embedding.subtype _)`.
We also record a reweighting lemma: given a weight function on finsets of `ι` defined as a
sum of indicator terms over a family `E ↦ g E`, sums against it reduce to sums over the
indexing family (so junk values of the old weights are never read). Finally, an
inclusion–exclusion formula for disjointness is used in Lemma 2.2(3).
-/

namespace Identities

/-- Lift a finset of the subtype `↥S` to a finset of `ι`. -/
abbrev liftSub (S : Finset ι) (E : Finset S) : Finset ι :=
  E.map (Function.Embedding.subtype (· ∈ S))

theorem mem_liftSub {S : Finset ι} {E : Finset S} {x : ι} :
    x ∈ liftSub S E ↔ ∃ h : x ∈ S, (⟨x, h⟩ : S) ∈ E := by
  simp [liftSub]

theorem liftSub_subset (S : Finset ι) (E : Finset S) : liftSub S E ⊆ S := by
  intro x hx
  obtain ⟨h, -⟩ := mem_liftSub.1 hx
  exact h

theorem disjoint_liftSub {S B : Finset ι} (hSB : Disjoint S B) (E : Finset S) :
    Disjoint (liftSub S E) B :=
  hSB.mono_left (liftSub_subset S E)

/-- Zero sets of the subsequence correspond to zero sets of `u` (after lifting). -/
theorem isZeroSet_liftSub_iff (u : ι → G) (S : Finset ι) (E : Finset S) :
    IsZeroSet u (liftSub S E) ↔ IsZeroSet (fun i : S => u i) E := by
  simp [IsZeroSet, liftSub, Finset.sum_map]

/-- The disjoint union of two zero sets is a zero set. -/
theorem isZeroSet_union {u : ι → G} {E F : Finset ι} [DecidableEq ι] (hE : IsZeroSet u E)
    (hF : IsZeroSet u F) (h : Disjoint E F) : IsZeroSet u (E ∪ F) :=
  ⟨hE.1.mono subset_union_left, by rw [sum_union h, hE.2, hF.2, add_zero]⟩

/-- Reweighting: if `c' F = ∑_{E ∈ A} [g E = F] * c E`, and every `g E` lies in `Z`, then
`∑_{F ∈ Z} c' F * f F = ∑_{E ∈ A} c E * f (g E)`. -/
theorem sum_mul_reweight {α β R : Type*} [CommRing R] [DecidableEq β] (Z : Finset β)
    (A : Finset α) (g : α → β) (hg : ∀ E ∈ A, g E ∈ Z) (c : α → R) (f : β → R) :
    ∑ F ∈ Z, (∑ E ∈ A, if g E = F then c E else 0) * f F = ∑ E ∈ A, c E * f (g E) := by
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun E hE => ?_
  simp_rw [ite_mul, zero_mul]
  rw [sum_ite_eq]
  simp [hg E hE]

/-- Inclusion–exclusion for disjointness, weighted by `c`:
`∑_E c E [J' ∩ E = ∅] = ∑_{K ⊆ J'} (-1)^{#K} ∑_{E ⊇ K} c E`. -/
theorem sum_ite_disjoint_eq {α β : Type*} [DecidableEq α] (A : Finset (Finset α))
    (c : Finset α → β) [CommRing β] (J' : Finset α) :
    ∑ E ∈ A, (if Disjoint J' E then c E else 0) =
      ∑ K ∈ J'.powerset, ((-1 : ℤ) ^ #K : β) * ∑ E ∈ A with K ⊆ E, c E := by
  have h : ∀ E : Finset α, (if Disjoint J' E then (1 : ℤ) else 0) =
      ∑ K ∈ J'.powerset, if K ⊆ E then (-1 : ℤ) ^ #K else 0 := by
    intro E
    rw [← sum_filter]
    have : J'.powerset.filter (· ⊆ E) = (J' ∩ E).powerset := by
      ext K; simp [subset_inter_iff]
    rw [this, sum_powerset_neg_one_pow_card]
    simp only [disjoint_iff_inter_eq_empty]
  simp_rw [mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun E _ => ?_
  have := congrArg (fun z : ℤ => (z : β) * c E) (h E)
  simp only [Int.cast_sum, apply_ite (Int.cast : ℤ → β), Int.cast_one, Int.cast_zero, ite_mul,
    one_mul, zero_mul, sum_mul] at this
  rw [this]
  refine sum_congr rfl fun K _ => ?_
  split_ifs <;> simp

end Identities

open Identities

/-!
## Proof of Lemma 2.2(1)

The identity is the inclusion–exclusion one: for every nonempty `S ⊆ Fin (t + 1)` the union
`⋃_{k ∈ S} B k` is a zero set, and it receives the weight `(-1) ^ (#S + 1)`. Weights of repeated
unions add up.
-/

/-- **Lemma 2.2(1)**: `t + 1` pairwise disjoint zero sets give an
integral `𝓘_t`-identity. -/
theorem hasIncidenceIdentity_of_pairwise_disjoint [Fintype ι] (u : ι → G) (t : ℕ)
    (B : Fin (t + 1) → Finset ι) (hB : ∀ k, IsZeroSet u (B k))
    (hdisj : Pairwise (Function.onFun Disjoint B)) :
    HasIncidenceIdentity ℤ u t := by
  classical
  -- The union of the blocks indexed by `S`, the nonempty index sets, and the signs.
  set U : Finset (Fin (t + 1)) → Finset ι := fun S => S.biUnion B with hU
  set T : Finset (Finset (Fin (t + 1))) := univ.filter Finset.Nonempty with hT
  set f : Finset (Fin (t + 1)) → ℤ := fun S => (-1) ^ (#S + 1) with hf
  clear_value U T f
  have hUz : ∀ S ∈ T, U S ∈ zeroSets u := by
    intro S hS
    obtain ⟨k, hk⟩ := (mem_filter.1 (hT ▸ hS)).2
    simp only [zeroSets, mem_filter, mem_univ, true_and]
    refine ⟨(hB k).1.mono (hU ▸ subset_biUnion_of_mem B hk), ?_⟩
    rw [hU, sum_biUnion (hdisj.set_pairwise _)]
    exact sum_eq_zero fun k _ => (hB k).2
  -- Summing `c` over the zero sets with a property `P` is summing `f` over the `S` with `P (U S)`.
  have key : ∀ (P : Finset ι → Prop) [DecidablePred P],
      ∑ E ∈ zeroSets u with P E, ∑ S ∈ T with U S = E, f S = ∑ S ∈ T with P (U S), f S := by
    intro P _
    rw [← sum_fiberwise_of_maps_to (s := T.filter fun S => P (U S))
      (t := (zeroSets u).filter P) (g := U)]
    · refine sum_congr rfl fun E hE => ?_
      rw [filter_filter]
      refine sum_congr ?_ fun _ _ => rfl
      ext S
      simp only [mem_filter]
      constructor
      · rintro ⟨hS, rfl⟩
        exact ⟨hS, (mem_filter.1 hE).2, rfl⟩
      · rintro ⟨hS, -, h⟩
        exact ⟨hS, h⟩
    · intro S hS
      rw [mem_filter] at hS ⊢
      exact ⟨hUz S hS.1, hS.2⟩
  refine ⟨fun E => ∑ S ∈ T with U S = E, f S, ?_, ?_⟩
  · -- The total weight is `∑_{S ≠ ∅} (-1) ^ (#S + 1) = 1`.
    have h1 := key (fun _ => True)
    simp only [filter_true] at h1
    rw [h1]
    have h0 : ∑ S : Finset (Fin (t + 1)), (-1 : ℤ) ^ #S = 0 := by
      rw [← powerset_univ]
      exact sum_powerset_neg_one_pow_card_of_nonempty univ_nonempty
    rw [← sum_filter_add_sum_filter_not univ Finset.Nonempty] at h0
    have hempty : (univ.filter fun S : Finset (Fin (t + 1)) => ¬ S.Nonempty) = {∅} := by
      ext S
      simp [not_nonempty_iff_eq_empty]
    rw [hempty, sum_singleton, card_empty, pow_zero] at h0
    simp only [hf, pow_succ, mul_neg_one, sum_neg_distrib]
    rw [hT]
    linarith
  · -- The moments vanish by toggling a block that misses `J`.
    intro J hJ1 hJt
    rw [key (J ⊆ ·)]
    have hJne : J.Nonempty := card_pos.1 hJ1
    obtain ⟨k0, hk0⟩ : ∃ k0, Disjoint J (B k0) := by
      by_contra hcon
      push Not at hcon
      have hne : ∀ k, (J ∩ B k).Nonempty := fun k =>
        not_disjoint_iff_nonempty_inter.1 (hcon k)
      choose g hg using hne
      have hle : #(univ : Finset (Fin (t + 1))) ≤ #J := by
        refine card_le_card_of_injOn g (fun k _ => (mem_inter.1 (hg k)).1) ?_
        intro a _ b _ hab
        by_contra hne
        exact disjoint_left.1 (hdisj hne) (mem_inter.1 (hg a)).2
          (hab ▸ (mem_inter.1 (hg b)).2)
      rw [card_univ, Fintype.card_fin] at hle
      omega
    have hnemp : ∀ S, J ⊆ U S → S.Nonempty := by
      intro S hS
      obtain ⟨x, hx⟩ := hJne
      obtain ⟨k, hk, -⟩ := mem_biUnion.1 (hU ▸ hS hx)
      exact ⟨k, hk⟩
    -- `J ⊆ U S` is insensitive to toggling `k0`.
    have hins : ∀ S, J ⊆ U (insert k0 S) ↔ J ⊆ U S := by
      intro S
      simp only [hU, biUnion_insert]
      constructor
      · intro h x hx
        rcases mem_union.1 (h hx) with h' | h'
        · exact absurd h' (disjoint_left.1 hk0 hx)
        · exact h'
      · exact fun h => h.trans subset_union_right
    have hera : ∀ S, J ⊆ U (S.erase k0) ↔ J ⊆ U S := by
      intro S
      by_cases hk : k0 ∈ S
      · rw [← hins (S.erase k0), insert_erase hk]
      · rw [erase_eq_of_notMem hk]
    let tog : ∀ S ∈ T.filter (fun S => J ⊆ U S), Finset (Fin (t + 1)) :=
      fun S _ => if k0 ∈ S then S.erase k0 else insert k0 S
    refine sum_involution tog ?_ ?_ ?_ ?_
    · intro S _
      by_cases hk : k0 ∈ S
      · simp only [tog, hk, ite_true, hf]
        rw [← card_erase_add_one hk]
        ring
      · simp only [tog, hk, ite_false, hf]
        rw [card_insert_of_notMem hk]
        ring
    · intro S _ _
      by_cases hk : k0 ∈ S
      · simp only [tog, hk, ite_true]
        exact fun h => notMem_erase k0 S (h.symm ▸ hk)
      · simp only [tog, hk, ite_false]
        exact fun h => hk (h ▸ mem_insert_self k0 S)
    · intro S hS
      have hJS := (mem_filter.1 hS).2
      rw [hT]
      have hJ' : J ⊆ U (tog S hS) := by
        by_cases hk : k0 ∈ S
        · simp only [tog, hk, ite_true]
          exact (hera S).2 hJS
        · simp only [tog, hk, ite_false]
          exact (hins S).2 hJS
      exact mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hnemp _ hJ'⟩, hJ'⟩
    · intro S _
      by_cases hk : k0 ∈ S
      · simp [tog, hk]
      · simp [tog, hk]

/-! ## Proof of Lemma 2.2(2) -/

/-- **Lemma 2.2(2), Section 2** (finite-difference construction): for `t ≥ 1`, a zero set `B`
together with an
integral `𝓘_{t-1}`-identity on a subsequence disjoint from `B` gives an integral
`𝓘_t`-identity. -/
theorem hasIncidenceIdentity_of_disjoint_zeroSet [Fintype ι] (u : ι → G) {t : ℕ}
    (ht : 1 ≤ t) (B S : Finset ι) (hB : IsZeroSet u B) (hSB : Disjoint S B)
    (hS : HasIncidenceIdentity ℤ (fun i : S => u i) (t - 1)) :
    HasIncidenceIdentity ℤ u t := by
  classical
  obtain ⟨c, hc⟩ := hS
  set Z' := zeroSets (fun i : S => u i)
  have hlift : ∀ E ∈ Z', liftSub S E ∈ zeroSets u := fun E hE =>
    mem_zeroSets.2 <| (isZeroSet_liftSub_iff u S E).2 (mem_zeroSets.1 hE)
  have hliftB : ∀ E ∈ Z', liftSub S E ∪ B ∈ zeroSets u := fun E hE =>
    mem_zeroSets.2 <| isZeroSet_union (mem_zeroSets.1 (hlift E hE)) hB (disjoint_liftSub hSB E)
  let c' : Finset ι → ℤ := fun F =>
    (∑ E ∈ Z', if liftSub S E = F then c E else 0) -
      (∑ E ∈ Z', if liftSub S E ∪ B = F then c E else 0) + if B = F then 1 else 0
  have key : ∀ f : Finset ι → ℤ, ∑ F ∈ zeroSets u, c' F * f F =
      ∑ E ∈ Z', c E * f (liftSub S E) - ∑ E ∈ Z', c E * f (liftSub S E ∪ B) + f B := by
    intro f
    simp only [c', add_mul, sub_mul, sum_add_distrib, sum_sub_distrib]
    rw [sum_mul_reweight _ _ _ hlift, sum_mul_reweight _ _ _ hliftB]
    simp_rw [ite_mul, one_mul, zero_mul]
    rw [sum_ite_eq]
    simp [mem_zeroSets.2 hB]
  -- Lemma 2.1(1): it suffices to reproduce evaluation of every polynomial at zero.
  refine ⟨c', (isIncidenceIdentity_iff_eval u t c').2 ?_⟩
  intro P hP
  -- Section 2: multilinearise P on Boolean inputs, then restrict
  -- P(z + 1_B) - P(z) to the coordinates of the old subsequence S.
  -- Terms not meeting B cancel; each surviving term has lost at least one degree.
  have hDlt : (PolynomialLifting.finiteDifference P S B).totalDegree < t :=
    (PolynomialLifting.degree_finiteDifference P S B hP).trans_lt
      (Nat.sub_lt ht (by decide))
  have hD := (isIncidenceIdentity_iff_eval (fun i : S => u i) (t - 1) c).1 hc
    (PolynomialLifting.finiteDifference P S B)
    (Nat.le_sub_one_of_lt hDlt)
  have hD0 : MvPolynomial.eval 0 (PolynomialLifting.finiteDifference P S B) =
      MvPolynomial.eval ((B : Set ι).indicator 1) P - MvPolynomial.eval 0 P := by
    simpa using PolynomialLifting.eval_finiteDifference P S B hSB ∅
  -- Apply the old identity to this lower-degree polynomial and rearrange.
  simp_rw [PolynomialLifting.eval_finiteDifference P S B hSB, mul_sub] at hD
  rw [sum_sub_distrib, hD0] at hD
  rw [key]
  change (∑ E ∈ Z', c E * MvPolynomial.eval ((liftSub S E : Set ι).indicator 1) P) -
      (∑ E ∈ Z', c E * MvPolynomial.eval (((liftSub S E ∪ B : Finset ι) : Set ι).indicator 1) P) +
      MvPolynomial.eval ((B : Set ι).indicator 1) P = MvPolynomial.eval 0 P
  linear_combination -hD

/-!
## Proof of Lemma 2.2(3)

With `s = (-1) ^ t` and `c` the old identity on `T` (read only on the zero sets of the
subsequence), the new weights are `c E` on `lift E`, `-s * c E` on `Z \ lift E`, and `s` on `Z`.
The moment conditions are checked directly via inclusion–exclusion.
-/

/-- **Lemma 2.2(3)**: for `t ≥ 1`, an integral `𝓘_{t-1}`-identity on a
proper subsequence `T ⊊ Z` of a zero set `Z` gives an integral `𝓘_t`-identity. -/
theorem hasIncidenceIdentity_of_ssubset_zeroSet [Fintype ι] (u : ι → G) {t : ℕ}
    (ht : 1 ≤ t) (Z T : Finset ι) (hZ : IsZeroSet u Z) (hTZ : T ⊂ Z)
    (hT : HasIncidenceIdentity ℤ (fun i : T => u i) (t - 1)) :
    HasIncidenceIdentity ℤ u t := by
  classical
  obtain ⟨c, hc1, hcJ⟩ := hT
  set Z' := zeroSets (fun i : T => u i)
  set s : ℤ := (-1) ^ t with hs
  have hss : s * s = 1 := by rw [hs, ← mul_pow]; simp
  have hTZ' : T ⊆ Z := hTZ.subset
  obtain ⟨x₀, hx₀Z, hx₀T⟩ := exists_of_ssubset hTZ
  have hlift : ∀ E ∈ Z', liftSub T E ∈ zeroSets u := fun E hE =>
    mem_zeroSets.2 <| (isZeroSet_liftSub_iff u T E).2 (mem_zeroSets.1 hE)
  have hcomp : ∀ E ∈ Z', Z \ liftSub T E ∈ zeroSets u := by
    intro E hE
    refine mem_zeroSets.2 ⟨⟨x₀, mem_sdiff.2 ⟨hx₀Z, fun h => hx₀T (liftSub_subset T E h)⟩⟩, ?_⟩
    have h1 := sum_sdiff (f := u) ((liftSub_subset T E).trans hTZ')
    rw [hZ.2, (mem_zeroSets.1 (hlift E hE)).2, add_zero] at h1
    exact h1
  let c' : Finset ι → ℤ := fun F =>
    (∑ E ∈ Z', if liftSub T E = F then c E else 0) -
      s * (∑ E ∈ Z', if Z \ liftSub T E = F then c E else 0) + s * if Z = F then 1 else 0
  have key : ∀ f : Finset ι → ℤ, ∑ F ∈ zeroSets u, c' F * f F =
      ∑ E ∈ Z', c E * f (liftSub T E) - s * ∑ E ∈ Z', c E * f (Z \ liftSub T E) + s * f Z := by
    intro f
    simp only [c', add_mul, sub_mul, mul_assoc, sum_add_distrib, sum_sub_distrib, ← mul_sum]
    rw [sum_mul_reweight _ _ _ hlift, sum_mul_reweight _ _ _ hcomp]
    simp_rw [ite_mul, one_mul, zero_mul]
    rw [sum_ite_eq]
    simp [mem_zeroSets.2 hZ]
  refine ⟨c', ?_, fun J hJ1 hJt => ?_⟩
  · have := key (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hc1]
    ring
  · have hm := key (fun F => if J ⊆ F then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at hm
    rw [sum_filter, hm]
    by_cases hJZ : J ⊆ Z
    swap
    · have h1 : ∀ E : Finset T, ¬ J ⊆ liftSub T E := fun E h =>
        hJZ (h.trans ((liftSub_subset T E).trans hTZ'))
      have h2 : ∀ E : Finset T, ¬ J ⊆ Z \ liftSub T E := fun E h => hJZ (h.trans sdiff_subset)
      simp [h1, h2, hJZ]
    set J' : Finset T := J.subtype (· ∈ T) with hJ'
    have hD : ∀ E : Finset T, J ⊆ Z \ liftSub T E ↔ Disjoint J' E := by
      intro E
      rw [subset_sdiff, and_iff_right hJZ, disjoint_left, disjoint_left]
      constructor
      · intro h y hy hyE
        rw [hJ', mem_subtype] at hy
        exact h hy (mem_liftSub.2 ⟨y.2, hyE⟩)
      · intro h x hx hxL
        obtain ⟨hxT, hxE⟩ := mem_liftSub.1 hxL
        exact h (by rw [hJ', mem_subtype]; exact hx) hxE
    have hL : ∀ E : Finset T, J ⊆ liftSub T E ↔ J ⊆ T ∧ J' ⊆ E := by
      intro E
      constructor
      · intro h
        refine ⟨h.trans (liftSub_subset T E), fun y hy => ?_⟩
        rw [hJ', mem_subtype] at hy
        obtain ⟨_, h'⟩ := mem_liftSub.1 (h hy)
        exact h'
      · rintro ⟨hJT, h⟩ x hx
        exact mem_liftSub.2 ⟨hJT hx, h (by rw [hJ', mem_subtype]; exact hx)⟩
    simp only [hD, hL, hJZ, ite_true]
    rw [sum_ite_disjoint_eq Z' c J']
    simp only [Int.cast_id]
    have hcardJ' : #J' ≤ #J := by rw [hJ', card_subtype]; exact card_filter_le _ _
    have hM : ∀ K : Finset T, 1 ≤ #K → #K ≤ t - 1 → ∑ E ∈ Z' with K ⊆ E, c E = 0 :=
      fun K h1 h2 => by convert hcJ K h1 h2
    have hM0 : ∑ E ∈ Z' with ∅ ⊆ E, c E = 1 := by
      rw [filter_true_of_mem (fun _ _ => empty_subset _)]; exact hc1
    by_cases hsmall : #J' ≤ t - 1
    · have hA : ∑ K ∈ J'.powerset, (-1 : ℤ) ^ #K * ∑ E ∈ Z' with K ⊆ E, c E = 1 := by
        rw [sum_eq_single ∅]
        · simp [hc1]
        · intro K hK hKne
          rw [hM K (card_pos.2 (nonempty_iff_ne_empty.2 hKne))
            ((card_le_card (mem_powerset.1 hK)).trans hsmall), mul_zero]
        · intro h
          exact absurd (empty_mem_powerset J') h
      rw [hA]
      by_cases hJT : J ⊆ T
      · have hJ'c : #J' = #J := by rw [hJ', card_subtype, filter_true_of_mem hJT]
        simp only [hJT, true_and]
        rw [← sum_filter, hM J' (hJ'c ▸ hJ1) hsmall]
        ring
      · simp [hJT]
    · have hJ'eq : #J' = #J := by omega
      have hJt' : #J' = t := by omega
      have hJT : J ⊆ T := by
        rw [hJ', card_subtype] at hJ'eq
        intro x hx
        exact filter_card_eq hJ'eq x hx
      have hJ'ne : (∅ : Finset T) ≠ J' := by
        intro h
        rw [← h, card_empty] at hJt'
        omega
      have hA : ∑ K ∈ J'.powerset, (-1 : ℤ) ^ #K * ∑ E ∈ Z' with K ⊆ E, c E =
          1 + s * ∑ E ∈ Z' with J' ⊆ E, c E := by
        rw [sum_eq_add ∅ J' hJ'ne]
        · simp [hc1, hJt', hs]
        · intro K hK hKne
          have hlt : #K < #J' :=
            card_lt_card (ssubset_of_subset_of_ne (mem_powerset.1 hK) hKne.2)
          rw [hM K (card_pos.2 (nonempty_iff_ne_empty.2 hKne.1)) (by omega), mul_zero]
        · intro h
          exact absurd (empty_mem_powerset J') h
        · intro h
          exact absurd (mem_powerset_self J') h
      rw [hA]
      simp only [hJT, true_and]
      rw [← sum_filter]
      linear_combination (-∑ E ∈ Z' with J' ⊆ E, c E) * hss

end DavenportProject
