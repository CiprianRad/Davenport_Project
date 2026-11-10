/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Defs

/-!
# Lemma 2.1(1) and (2)

* `isIncidenceIdentity_iff_eval` (Lemma 2.1(1)): `c` is an `𝓘_t`-identity iff
  `∑_E c_E P(𝟙_E) = P(0)` for every polynomial `P` of degree at most `t`, proved through
  multilinear reduction on the Boolean cube.
* `IsIncidenceIdentity.intCast` (Lemma 2.1(2)): an integral identity maps to an identity over every
  commutative ring.
-/

public section

namespace DavenportProject

open Finset MvPolynomial

/-!
## Evaluating polynomials at indicator vectors of finite sets

Helper lemmas for Lemma 2.1(1): evaluating a monomial `X^m` at the indicator `𝟙_E` of a
finite set gives `[supp m ⊆ E]`, and the number of variables occurring in a monomial is at most
its degree.
-/

namespace Identities

variable {R : Type*} [CommSemiring R] {ι : Type*}

/-- Evaluating a monomial at the indicator vector of `E` gives its coefficient when the
support of its exponent lies in `E`, and `0` otherwise. -/
theorem eval_indicator_monomial (E : Finset ι) (m : ι →₀ ℕ) (a : R) [Decidable (m.support ⊆ E)] :
    eval ((E : Set ι).indicator 1) (monomial m a) = if m.support ⊆ E then a else 0 := by
  classical
  rw [eval_monomial, Finsupp.prod]
  have : ∏ i ∈ m.support, (E : Set ι).indicator (1 : ι → R) i ^ m i =
      ∏ i ∈ m.support, (if i ∈ E then (1 : R) else 0) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp hi
    by_cases hiE : i ∈ E
    · simp [hiE]
    · simp [hiE, zero_pow hmi]
  rw [this, Finset.prod_boole]
  by_cases h : m.support ⊆ E
  · have h' : ∀ i ∈ m.support, i ∈ E := fun i hi => h hi
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h'), mul_one]
  · have h' : ¬∀ i ∈ m.support, i ∈ E := fun h' => h h'
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h'),
      mul_zero]

/-- The number of variables occurring in `X^m` is at most its degree. -/
theorem card_support_le_sum (m : ι →₀ ℕ) : #m.support ≤ m.sum fun _ e => e := by
  rw [Finsupp.sum, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

/-- A product of distinct variables has total degree at most the number of variables. -/
theorem totalDegree_prod_X_le (J : Finset ι) :
    (∏ j ∈ J, X j : MvPolynomial ι R).totalDegree ≤ #J := by
  refine (totalDegree_finsetProd _ _).trans ?_
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [X]
  exact (totalDegree_monomial_le _ _).trans (by simp)

end Identities

variable {G : Type*} [AddCommGroup G] {ι : Type*}

open Identities in
/-- **Lemma 2.1(1), Section 2**: `c` is an `𝓘_t`-identity over `R` iff
`∑_E c_E P(𝟙_E) = P(0)` for every polynomial `P` of degree at most `t`. -/
theorem isIncidenceIdentity_iff_eval {R : Type*} [CommRing R] [Fintype ι] (u : ι → G)
    (t : ℕ) (c : Finset ι → R) :
    IsIncidenceIdentity R u t c ↔
      ∀ P : MvPolynomial ι R, P.totalDegree ≤ t →
        ∑ E ∈ zeroSets u, c E * MvPolynomial.eval ((E : Set ι).indicator 1) P =
          MvPolynomial.eval 0 P := by
  classical
  constructor
  · rintro ⟨h1, hJ⟩ P hP
    -- Boolean multilinear reduction replaces each exponent vector by its support.
    -- The moment `∑_{E ⊇ supp m} c E` vanishes unless `m = 0`.
    have key : ∀ m ∈ P.support,
        ∑ E ∈ zeroSets u, c E * (if m.support ⊆ E then P.coeff m else 0) =
          if m = 0 then P.coeff m else 0 := by
      intro m hm
      simp_rw [mul_ite, mul_zero]
      rw [← Finset.sum_filter, ← Finset.sum_mul]
      by_cases hm0 : m = 0
      · subst hm0
        simp [h1]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hm0)]
        have hcard : 1 ≤ #m.support :=
          Finset.card_pos.mpr (Finsupp.support_nonempty_iff.mpr hm0)
        have hle : #m.support ≤ t :=
          (card_support_le_sum m).trans ((le_totalDegree hm).trans hP)
        rw [hJ _ hcard hle, zero_mul]
    conv_lhs => rw [P.as_sum]
    simp_rw [map_sum, eval_indicator_monomial, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl key, Finset.sum_ite_eq' P.support 0,
      MvPolynomial.eval_zero, constantCoeff_eq]
    split_ifs with h0
    · rfl
    · exact (notMem_support_iff.mp h0).symm
  · intro h
    refine ⟨?_, fun J hJ1 hJt => ?_⟩
    · simpa using h 1 (by simp)
    · have := h (∏ j ∈ J, X j) ((totalDegree_prod_X_le J).trans hJt)
      obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp hJ1
      rw [show eval 0 (∏ j ∈ J, X j : MvPolynomial ι R) = 0 by
        rw [map_prod]; exact Finset.prod_eq_zero hj₀ (by simp)] at this
      rw [← this, Finset.sum_filter]
      refine Finset.sum_congr rfl fun E _ => ?_
      rw [map_prod]
      simp_rw [eval_X]
      have : ∏ j ∈ J, (E : Set ι).indicator (1 : ι → R) j =
          ∏ j ∈ J, (if j ∈ E then (1 : R) else 0) :=
        Finset.prod_congr rfl fun j _ => by simp [Set.indicator_apply]
      rw [this, Finset.prod_boole]
      by_cases hJE : J ⊆ E
      · have h' : ∀ j ∈ J, j ∈ E := fun j hj => hJE hj
        rw [ite_eq_left_of_eq_true _ _ (eq_true hJE), ite_eq_left_of_eq_true _ _ (eq_true h'),
          mul_one]
      · have h' : ¬∀ j ∈ J, j ∈ E := fun h' => hJE h'
        rw [ite_eq_right_of_eq_false _ _ (eq_false hJE), ite_eq_right_of_eq_false _ _ (eq_false h'),
          mul_zero]

/-- **Lemma 2.1(2), Section 2**: an integral `𝓘_t`-identity is an `𝓘_t`-identity
over every commutative ring, by reduction of the coefficients. -/
theorem IsIncidenceIdentity.intCast (R : Type*) [CommRing R] [Fintype ι] {u : ι → G}
    {t : ℕ} {c : Finset ι → ℤ} (hc : IsIncidenceIdentity ℤ u t c) :
    IsIncidenceIdentity R u t (fun E => (c E : R)) := by
  classical
  unfold IsIncidenceIdentity at hc ⊢
  obtain ⟨h1, h2⟩ := hc
  refine ⟨?_, fun J hJ1 hJt => ?_⟩
  · rw [← Int.cast_sum]
    convert congrArg (Int.cast : ℤ → R) h1 using 2
    · simp
  · rw [← Int.cast_sum]
    convert congrArg (Int.cast : ℤ → R) (h2 J hJ1 hJt) using 2
    · simp

end DavenportProject
