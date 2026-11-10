/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DavenportProject.Identities.Evaluation

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

end DavenportProject.Identities.PolynomialLifting
