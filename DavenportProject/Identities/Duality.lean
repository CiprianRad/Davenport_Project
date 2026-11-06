/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George C. Rad
-/
module

public import DavenportProject.Defs
import DavenportProject.Identities.Evaluation
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Lemma 2.1(3)

`hasIncidenceIdentity_iff_not_hasSeparator`: over a field, a sequence has an `𝓘_t`-identity iff it
has no separator of degree `t` (linear duality).
-/

/-!
## Proof of Lemma 2.1(3)

The forward direction applies Lemma 2.1(1) to a separator. For the converse, an identity is
a solution `c` of `∑_E c_E v_E = e` in `Finset ι → K`, where `v_E J = [E ∈ 𝒵(u), #J ≤ t, J ⊆ E]`
and `e J = [J = ∅]`; if there is none, a linear functional separating `e` from the span of
the `v_E` gives the coefficients of a separator `∑_{#J ≤ t} φ_J ∏_{j ∈ J} X_j`.
-/

public section

namespace DavenportProject.Identities

open Finset MvPolynomial

variable {G : Type*} [AddCommGroup G] {ι : Type*}

/-- Evaluating a product of distinct variables at the indicator of `E` gives `[J ⊆ E]`. -/
theorem eval_indicator_prod_X {K : Type*} [CommSemiring K] (E J : Finset ι)
    [Decidable (J ⊆ E)] :
    eval ((E : Set ι).indicator 1) (∏ j ∈ J, X j : MvPolynomial ι K) =
      if J ⊆ E then 1 else 0 := by
  classical
  rw [map_prod]
  simp only [eval_X, Set.indicator_apply, Finset.mem_coe, Pi.one_apply]
  rw [Finset.prod_boole]
  by_cases h : J ⊆ E
  · have h' : ∀ i ∈ J, i ∈ E := fun i hi => h hi
    rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true h)]
  · have h' : ¬∀ i ∈ J, i ∈ E := fun h' => h fun i hi => h' i hi
    rw [ite_eq_right_of_eq_false _ _ (eq_false h'), ite_eq_right_of_eq_false _ _ (eq_false h)]

end DavenportProject.Identities

end

public section

namespace DavenportProject

open Finset MvPolynomial
open DavenportProject.Identities

open Finset

variable {G : Type*} [AddCommGroup G] {ι : Type*}

/-- **Lemma 2.1(3)**: over a field, `u` has an `𝓘_t`-identity iff it
has no separator of degree `t`. -/
theorem hasIncidenceIdentity_iff_not_hasSeparator (K : Type*) [Field K] [Fintype ι]
    (u : ι → G) (t : ℕ) :
    HasIncidenceIdentity K u t ↔ ¬ HasSeparator K u t := by
  classical
  constructor
  · rintro ⟨c, hc⟩ ⟨P, hdeg, h0, hE⟩
    have key := (DavenportProject.isIncidenceIdentity_iff_eval u t c).1 hc P hdeg
    rw [h0, Finset.sum_eq_zero] at key
    · exact zero_ne_one key
    · intro E hE'
      rw [hE E (by simpa [zeroSets] using hE'), mul_zero]
  · intro hP
    by_contra hI
    apply hP
    let v : Finset ι → Finset ι → K := fun E J =>
      if E ∈ zeroSets u ∧ #J ≤ t ∧ J ⊆ E then 1 else 0
    let e : Finset ι → K := fun J => if J = ∅ then 1 else 0
    have hcoord : ∀ (c : Finset ι → K) (J : Finset ι), #J ≤ t →
        (∑ E, c E • v E) J = ∑ E ∈ zeroSets u with J ⊆ E, c E := by
      intro c J hJ
      rw [Finset.sum_apply, Finset.sum_filter]
      simp only [Pi.smul_apply, smul_eq_mul, v, hJ, true_and, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      congr 1
      ext E
      simp
    have he : e ∉ Submodule.span K (Set.range v) := by
      intro h
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 h
      refine hI ⟨c, ?_, fun J hJ1 hJt => ?_⟩
      · have h1 := hcoord c ∅ (by simp)
        rw [hc] at h1
        simpa [e] using h1.symm
      · have h1 := hcoord c J hJt
        rw [hc] at h1
        have hJ : J ≠ ∅ := by
          rintro rfl
          simp at hJ1
        simpa [e, hJ] using h1.symm
    obtain ⟨φ, hφe, hφp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem he inferInstance
    have hφv : ∀ E, φ (v E) = 0 := fun E => by
      have hmem : φ (v E) ∈ (Submodule.span K (Set.range v)).map φ :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨E, rfl⟩)
      rw [hφp] at hmem
      exact (Submodule.mem_bot K).1 hmem
    let δ : Finset ι → Finset ι → K := fun J J' => if J = J' then 1 else 0
    have hφsum : ∀ x : Finset ι → K, φ x = ∑ J, x J * φ (δ J) := fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      rfl
    let P : MvPolynomial ι K :=
      ∑ J ∈ univ.filter (fun J : Finset ι => #J ≤ t), C (φ (δ J) / φ e) * ∏ j ∈ J, X j
    have hev : ∀ E : Finset ι, eval ((E : Set ι).indicator 1) P =
        (∑ J, (if #J ≤ t ∧ J ⊆ E then 1 else 0) * φ (δ J)) / φ e := by
      intro E
      simp only [P, map_sum, map_mul, eval_C, eval_indicator_prod_X]
      rw [Finset.sum_div, Finset.sum_filter]
      refine Finset.sum_congr rfl fun J _ => ?_
      by_cases h1 : #J ≤ t <;> by_cases h2 : J ⊆ E <;> simp [h1, h2, div_eq_mul_inv]
    refine ⟨P, ?_, ?_, fun E hE => ?_⟩
    · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun J hJ => ?_)
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (Identities.totalDegree_prod_X_le J).trans (Finset.mem_filter.1 hJ).2
    · have h0 : (0 : ι → K) = ((∅ : Finset ι) : Set ι).indicator 1 := by
        ext i
        simp
      rw [h0, hev, ← div_self hφe]
      congr 1
      rw [hφsum e]
      refine Finset.sum_congr rfl fun J _ => ?_
      by_cases hJ : J = ∅
      · subst hJ
        simp [e]
      · simp [e, hJ]
    · have hE' : E ∈ zeroSets u := by simpa [zeroSets] using hE
      have hsum := hφsum (v E)
      rw [hφv E] at hsum
      have hnum : ∑ J, (if #J ≤ t ∧ J ⊆ E then (1 : K) else 0) * φ (δ J) = 0 := by
        exact (Finset.sum_congr rfl fun J _ => by simp [v, hE']).trans hsum.symm
      rw [hev, hnum, zero_div]

end DavenportProject

end
