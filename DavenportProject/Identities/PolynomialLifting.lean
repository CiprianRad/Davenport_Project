/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DavenportProject.Identities.Evaluation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Ring

/-!
# Polynomial degree cancellations in Lemma 2.2, Section 2

We multilinearise monomials by replacing their exponent vectors by their supports,
as in Lemma 2.1(1). The following polynomials write out the cancellations in the
paper's finite-difference and complement arguments. Their evaluations are stated
on Boolean vectors, precisely the evaluations used by an incidence identity.
-/

public section

namespace DavenportProject.Identities.PolynomialLifting

open Finset MvPolynomial

variable {ι : Type*}

/-- The squarefree monomial indexed by `J`. -/
noncomputable def squarefree (J : Finset ι) : MvPolynomial ι ℤ := ∏ i ∈ J, X i

theorem degree_squarefree (J : Finset ι) : (squarefree J).totalDegree ≤ #J :=
  Identities.totalDegree_prod_X_le J

open Classical in
theorem eval_squarefree (J E : Finset ι) :
    eval ((E : Set ι).indicator 1) (squarefree J) = if J ⊆ E then 1 else 0 := by
  classical
  simp only [squarefree, map_prod, eval_X, Set.indicator_apply, Pi.one_apply]
  rw [prod_boole]
  rfl

open Classical in
/-- The unchanged Boolean evaluations after replacing each exponent vector by its support.
This is the monomial form of Boolean multilinearisation used in Lemma 2.1(1). -/
theorem eval_as_squarefree (P : MvPolynomial ι ℤ) (E : Finset ι) :
    eval ((E : Set ι).indicator 1) P =
      ∑ m ∈ P.support, P.coeff m * (if m.support ⊆ E then 1 else 0) := by
  classical
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, Identities.eval_indicator_monomial]
  apply sum_congr rfl
  intro m hm
  split_ifs <;> simp

open Classical in
/-- The surviving monomial in `P(z+1_B)-P(z)`, restricted to the coordinates of `S`.
Terms not involving `B` cancel; terms involving a coordinate outside `S ∪ B` vanish. -/
noncomputable def differenceMonomial (S B J : Finset ι) : MvPolynomial S ℤ :=
  if J ⊆ S ∪ B ∧ ¬ J ⊆ S then squarefree (J.subtype (· ∈ S)) else 0

/-- **Lemma 2.2(2), Section 2:** a surviving term has spent at least one degree
outside `S`, on a coordinate of the disjoint zero set `B`. -/
theorem degree_differenceMonomial (S B J : Finset ι) {t : ℕ} (hJ : #J ≤ t) :
    (differenceMonomial S B J).totalDegree ≤ t - 1 := by
  classical
  unfold differenceMonomial
  split_ifs with h
  · apply (degree_squarefree _).trans
    rw [card_subtype]
    have hlt : #(J.filter (· ∈ S)) < #J := by
      apply card_lt_card
      apply filter_ssubset.mpr
      exact not_subset.mp h.2
    omega
  · simp

open Classical in
/-- Evaluating the cancelled finite difference gives the difference of the
two original squarefree evaluations. -/
theorem eval_differenceMonomial (S B J : Finset ι) (hSB : Disjoint S B)
    (E : Finset S) :
    eval ((E : Set S).indicator 1) (differenceMonomial S B J) =
      (if J ⊆ E.map (Function.Embedding.subtype (· ∈ S)) ∪ B then (1 : ℤ) else 0) -
      (if J ⊆ E.map (Function.Embedding.subtype (· ∈ S)) then (1 : ℤ) else 0) := by
  classical
  let L := E.map (Function.Embedding.subtype (· ∈ S))
  have hLS : L ⊆ S := by intro x hx; obtain ⟨y, hy, rfl⟩ := mem_map.mp hx; exact y.2
  change eval ((E : Set S).indicator 1) (differenceMonomial S B J) =
    (if J ⊆ L ∪ B then 1 else 0) - (if J ⊆ L then 1 else 0)
  by_cases hJS : J ⊆ S
  · have hiff : J ⊆ L ∪ B ↔ J ⊆ L := by
      constructor
      · intro h x hx
        rcases mem_union.mp (h hx) with hxL | hxB
        · exact hxL
        · exact False.elim (disjoint_left.mp hSB (hJS hx) hxB)
      · exact fun h => h.trans subset_union_left
    simp [differenceMonomial, hJS, hiff]
  · have hJL : ¬ J ⊆ L := fun h => hJS (h.trans hLS)
    by_cases hJSB : J ⊆ S ∪ B
    · have hiff : J ⊆ L ∪ B ↔ J.subtype (· ∈ S) ⊆ E := by
        constructor
        · intro h y hy
          have hyJ : (y : ι) ∈ J := by simpa using hy
          rcases mem_union.mp (h hyJ) with hyL | hyB
          · simpa [L] using hyL
          · exact False.elim (disjoint_left.mp hSB y.2 hyB)
        · intro h x hx
          rcases mem_union.mp (hJSB hx) with hxS | hxB
          · apply mem_union_left
            have hxE := h (show (⟨x, hxS⟩ : S) ∈ J.subtype (· ∈ S) by simpa using hx)
            exact mem_map.mpr ⟨⟨x, hxS⟩, hxE, rfl⟩
          · exact mem_union_right _ hxB
      simp [differenceMonomial, hJSB, hJS, hJL, eval_squarefree, hiff]
    · have hnot : ¬ J ⊆ L ∪ B := fun h =>
        hJSB (h.trans (union_subset_union hLS subset_rfl))
      simp [differenceMonomial, hJSB, hnot, hJL]

/-- The paper's finite difference after Boolean multilinearisation, with the cancelled
monomials removed. Its variables are just the positions of the old subsequence. -/
noncomputable def finiteDifference (P : MvPolynomial ι ℤ) (S B : Finset ι) :
    MvPolynomial S ℤ :=
  ∑ m ∈ P.support, C (P.coeff m) * differenceMonomial S B m.support

/-- **Lemma 2.2(2), Section 2:** the restricted finite difference loses one degree. -/
theorem degree_finiteDifference (P : MvPolynomial ι ℤ) (S B : Finset ι)
    {t : ℕ} (hP : P.totalDegree ≤ t) :
    (finiteDifference P S B).totalDegree ≤ t - 1 := by
  apply totalDegree_finsetSum_le
  intro m hm
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact degree_differenceMonomial S B m.support
    ((Identities.card_support_le_sum m).trans ((le_totalDegree hm).trans hP))

open Classical in
/-- **Lemma 2.2(2), Section 2:** Boolean evaluation of the finite difference is
`P(1_(E ∪ B)) - P(1_E)`. -/
theorem eval_finiteDifference (P : MvPolynomial ι ℤ) (S B : Finset ι)
    (hSB : Disjoint S B) (E : Finset S) :
    eval ((E : Set S).indicator 1) (finiteDifference P S B) =
      eval (((E.map (Function.Embedding.subtype (· ∈ S)) ∪ B : Finset ι) : Set ι).indicator 1) P -
      eval (((E.map (Function.Embedding.subtype (· ∈ S)) : Finset ι) : Set ι).indicator 1) P := by
  classical
  simp only [finiteDifference, map_sum, map_mul, eval_C,
    eval_differenceMonomial S B _ hSB, eval_as_squarefree, mul_sub, sum_sub_distrib]

open Classical in
/-- All terms below the leading squarefree monomial in `∏ i ∈ J, (1-X i)`.
The leading term is `(-1)^|J| ∏ i ∈ J, X i`. -/
noncomputable def complementTail (J : Finset ι) : MvPolynomial ι ℤ :=
  ∑ K ∈ J.powerset.erase J, C ((-1 : ℤ) ^ #K) * squarefree K

/-- Expanding complementation isolates its degree-`|J|` term, as in the proof of
Lemma 2.2(3), Section 2. -/
theorem complement_expansion (J : Finset ι) :
    ∏ i ∈ J, (1 - X i : MvPolynomial ι ℤ) =
      C ((-1 : ℤ) ^ #J) * squarefree J + complementTail J := by
  classical
  rw [Finset.prod_sub]
  simp only [prod_const_one, mul_one]
  have hC : ∀ K : Finset ι, ((-1 : MvPolynomial ι ℤ) ^ #K) = C ((-1 : ℤ) ^ #K) := by
    intro K
    simp
  simp_rw [hC]
  exact (Finset.add_sum_erase J.powerset (fun K => C ((-1 : ℤ) ^ #K) * squarefree K)
    (mem_powerset_self J)).symm

/-- Every term remaining after the leading term is removed has strictly fewer
variables. This is the complement argument's degree cancellation. -/
theorem degree_complementTail (J : Finset ι) :
    (complementTail J).totalDegree ≤ #J - 1 := by
  classical
  apply totalDegree_finsetSum_le
  intro K hK
  obtain ⟨hne, hsub⟩ := mem_erase.mp hK
  have hlt : #K < #J := card_lt_card (ssubset_of_subset_of_ne (mem_powerset.mp hsub) hne)
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact (degree_squarefree K).trans (Nat.le_sub_one_of_lt hlt)

open Classical in
/-- Boolean evaluation of the lower-degree tail of the complement expansion. -/
theorem eval_complementTail (J E : Finset ι) :
    eval ((E : Set ι).indicator 1) (complementTail J) =
      (if Disjoint J E then (1 : ℤ) else 0) -
        (-1 : ℤ) ^ #J * (if J ⊆ E then 1 else 0) := by
  classical
  have hprod : eval ((E : Set ι).indicator 1) (∏ i ∈ J, (1 - X i : MvPolynomial ι ℤ)) =
      if Disjoint J E then (1 : ℤ) else 0 := by
    simp only [map_prod, map_sub, map_one, eval_X, Set.indicator_apply,
      Pi.one_apply, Finset.mem_coe]
    have hfactor (i : ι) : 1 - (if i ∈ E then (1 : ℤ) else 0) = if i ∉ E then 1 else 0 := by
      split_ifs <;> simp_all
    simp_rw [hfactor]
    rw [prod_boole]
    congr 1
    exact propext disjoint_left.symm
  rw [complement_expansion, map_add, map_mul, eval_C, eval_squarefree] at hprod
  omega

open Classical in
/-- The cancelled expression `z_J - (-1)^t (1-z)_J`, restricted to `T ⊆ Z`.
The coefficient of its possible degree-`t` term is displayed explicitly. -/
noncomputable def complementMonomial (t : ℕ) (T Z J : Finset ι) : MvPolynomial T ℤ :=
  let L := J.subtype (· ∈ T)
  if J ⊆ Z then
    C ((if J ⊆ T then 1 else 0) - (-1 : ℤ)^t * (-1 : ℤ)^#L) * squarefree L -
      C ((-1 : ℤ)^t) * complementTail L
  else 0

/-- **Lemma 2.2(3), Section 2:** complementation multiplies a top-degree
squarefree term by `(-1)^t`, so subtracting this signed complement cancels it. -/
theorem degree_complementMonomial (T Z J : Finset ι) {t : ℕ} (hJ : #J ≤ t) :
    (complementMonomial t T Z J).totalDegree ≤ t - 1 := by
  classical
  let L := J.subtype (· ∈ T)
  have hLJ : #L ≤ #J := by dsimp [L]; rw [card_subtype]; exact card_filter_le _ _
  have hL : #L ≤ t := hLJ.trans hJ
  have hfirst : (C ((if J ⊆ T then 1 else 0) - (-1 : ℤ)^t * (-1 : ℤ)^#L) *
      squarefree L).totalDegree ≤ t - 1 := by
    by_cases hsmall : #L ≤ t - 1
    · apply (totalDegree_mul _ _).trans
      rw [totalDegree_C, zero_add]
      exact (degree_squarefree L).trans hsmall
    · have hLt : #L = t := by omega
      have hLJ' : #L = #J := by omega
      have hJT : J ⊆ T := by
        dsimp [L] at hLJ'
        rw [card_subtype] at hLJ'
        exact filter_card_eq hLJ'
      have hsign : (-1 : ℤ)^t * (-1 : ℤ)^#L = 1 := by
        rw [hLt, ← mul_pow]
        simp
      simp [hJT, hsign]
  have htail : (C ((-1 : ℤ)^t) * complementTail L).totalDegree ≤ t - 1 := by
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, zero_add]
    exact (degree_complementTail L).trans (Nat.sub_le_sub_right hL 1)
  by_cases hJZ : J ⊆ Z
  · simpa only [complementMonomial, hJZ, ite_true] using
      (totalDegree_sub _ _).trans (max_le hfirst htail)
  · simp [complementMonomial, hJZ]

open Classical in
/-- Evaluating the cancelled complement polynomial is the difference between the
original and the signed complementary Boolean evaluations. -/
theorem eval_complementMonomial (t : ℕ) (T Z J : Finset ι) (hTZ : T ⊆ Z)
    (E : Finset T) :
    eval ((E : Set T).indicator 1) (complementMonomial t T Z J) =
      (if J ⊆ E.map (Function.Embedding.subtype (· ∈ T)) then (1 : ℤ) else 0) -
      (-1 : ℤ)^t *
        (if J ⊆ Z \ E.map (Function.Embedding.subtype (· ∈ T)) then (1 : ℤ) else 0) := by
  classical
  let L := E.map (Function.Embedding.subtype (· ∈ T))
  let J' := J.subtype (· ∈ T)
  have hLT : L ⊆ T := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    exact y.2
  have hL : J ⊆ L ↔ J ⊆ T ∧ J' ⊆ E := by
    constructor
    · intro h
      refine ⟨h.trans hLT, fun y hy => ?_⟩
      have hyJ : (y : ι) ∈ J := by simpa [J'] using hy
      simpa [L] using h hyJ
    · rintro ⟨hJT, h⟩ x hx
      exact mem_map.mpr ⟨⟨x, hJT hx⟩, h (by simpa [J'] using hx), rfl⟩
  change eval ((E : Set T).indicator 1) (complementMonomial t T Z J) =
    (if J ⊆ L then 1 else 0) - (-1 : ℤ)^t * (if J ⊆ Z \ L then 1 else 0)
  unfold complementMonomial
  by_cases hJZ : J ⊆ Z
  · have hD : J ⊆ Z \ L ↔ Disjoint J' E := by
      rw [subset_sdiff, and_iff_right hJZ, disjoint_left, disjoint_left]
      constructor
      · intro h y hy hyE
        have hyJ : (y : ι) ∈ J := by simpa [J'] using hy
        exact h hyJ (mem_map.mpr ⟨y, hyE, rfl⟩)
      · intro h x hx hxL
        obtain ⟨y, hyE, rfl⟩ := mem_map.mp hxL
        exact h (by simpa [J'] using hx) hyE
    simp only [hJZ, ite_true, map_sub, map_mul, eval_C, eval_squarefree,
      eval_complementTail]
    simp only [hL, hD]
    by_cases hJT : J ⊆ T
    · simp only [hJT, ite_true, true_and]
      dsimp only [J']
      ring_nf
    · simp only [hJT, ite_false, false_and]
      dsimp only [J']
      ring_nf
  · have hJL : ¬ J ⊆ L := fun h => hJZ ((h.trans hLT).trans hTZ)
    have hJcomp : ¬ J ⊆ Z \ L := fun h => hJZ (h.trans sdiff_subset)
    simp [hJZ, hJL, hJcomp]

/-- The polynomial `P(z)-(-1)^t P(1_Z-z)` from Lemma 2.2(3), after Boolean
multilinearisation and restriction to the old subsequence `T`. -/
noncomputable def complementDifference (P : MvPolynomial ι ℤ) (t : ℕ) (T Z : Finset ι) :
    MvPolynomial T ℤ :=
  ∑ m ∈ P.support, C (P.coeff m) * complementMonomial t T Z m.support

/-- **Lemma 2.2(3), Section 2:** the complement difference has degree at most `t-1`. -/
theorem degree_complementDifference (P : MvPolynomial ι ℤ) (T Z : Finset ι)
    {t : ℕ} (hP : P.totalDegree ≤ t) :
    (complementDifference P t T Z).totalDegree ≤ t - 1 := by
  apply totalDegree_finsetSum_le
  intro m hm
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact degree_complementMonomial T Z m.support
    ((Identities.card_support_le_sum m).trans ((le_totalDegree hm).trans hP))

open Classical in
/-- **Lemma 2.2(3), Section 2:** evaluation of the complement difference has the
paper's prescribed values on the old zero sets. -/
theorem eval_complementDifference (P : MvPolynomial ι ℤ) (t : ℕ) (T Z : Finset ι)
    (hTZ : T ⊆ Z) (E : Finset T) :
    eval ((E : Set T).indicator 1) (complementDifference P t T Z) =
      eval (((E.map (Function.Embedding.subtype (· ∈ T)) : Finset ι) : Set ι).indicator 1) P -
      (-1 : ℤ)^t *
        eval (((Z \ E.map (Function.Embedding.subtype (· ∈ T)) : Finset ι) : Set ι).indicator 1)
          P := by
  classical
  simp only [complementDifference, map_sum, map_mul, eval_C,
    eval_complementMonomial t T Z _ hTZ, eval_as_squarefree, mul_sub, sum_sub_distrib]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  ring

end DavenportProject.Identities.PolynomialLifting
