/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Sharpness
import DavenportProject.Identities.Evaluation
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.LinearCombination

/-!
# Remark 4.2, Section 4: the characteristic-two affine threshold

For five labels in `F₂³`, rank-nullity leaves two independent binary vectors in
the kernel of their label-sum map. An affine separator `1 + ℓ` would take linear
part value one at those vectors and their sum, contradicting additivity. The
four-term axis sequence supplies the matching lower bound.
-/

public section
namespace DavenportProject
namespace CharacteristicTwo
open Finset MvPolynomial

/-- A degree-at-most-one monomial is either constant or a single variable. -/
theorem exponent_degree_le_one {ι : Type*} (d : ι →₀ ℕ)
    (hd : d.sum (fun _ n => n) ≤ 1) : d = 0 ∨ ∃ i, d = Finsupp.single i 1 := by
  classical
  by_cases h0 : d = 0
  · exact Or.inl h0
  · right
    apply (Finsupp.sum_eq_one_iff d).1
    have hpos : d.sum (fun _ n => n) ≠ 0 := by
      intro h
      apply h0
      ext i
      by_cases hi : i ∈ d.support
      · exact (Finset.sum_eq_zero_iff.1 h) i hi
      · exact Finsupp.notMem_support_iff.1 hi
    omega

/-- **Remark 4.2, Section 4, affine form.** Removing the constant term from a
polynomial of total degree at most one gives an additive function. -/
theorem eval_add_of_totalDegree_le_one {ι K : Type*} [CommRing K]
    (P : MvPolynomial ι K) (hP : P.totalDegree ≤ 1) (x y : ι → K) :
    eval (x + y) P + eval 0 P = eval x P + eval y P := by
  classical
  have expand (z : ι → K) : eval z P =
      ∑ d ∈ P.support, eval z (monomial d (P.coeff d)) := by
    conv_lhs => rw [P.as_sum]
    simp only [map_sum]
  simp_rw [expand, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rcases exponent_degree_le_one d ((le_totalDegree hd).trans hP) with rfl | ⟨i, rfl⟩
  · simp
  · simp [eval_monomial, constantCoeff_monomial, mul_add]

/-- The two scalar values of the field `F₂`. -/
theorem binary_scalar (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- **Remark 4.2, Section 4.** The linear part `ℓ(z) = P(z) - P(0)` of an affine
polynomial over `F₂`; the preceding lemma proves additivity. -/
noncomputable def affineLinearPart {ι : Type*} (P : MvPolynomial ι (ZMod 2))
    (hP : P.totalDegree ≤ 1) : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := eval x P - eval 0 P
  map_add' x y := by
    have h := eval_add_of_totalDegree_le_one P hP x y
    linear_combination h
  map_smul' a x := by
    rcases binary_scalar a with rfl | rfl <;> simp

/-- The linear map in Remark 4.2: a binary vector selects and sums its labels. -/
noncomputable def labelSum (u : Fin 5 → (Fin 3 → ZMod 2)) :
    (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun z := ∑ j, z j • u j
  map_add' x y := by simp [add_smul, sum_add_distrib]
  map_smul' a x := by simp [smul_sum, mul_smul]

/-- **Remark 4.2, Section 4, rank-nullity.** Five binary coordinates mapping to
three binary coordinates leave a kernel of dimension at least two. -/
theorem two_le_finrank_ker (u : Fin 5 → (Fin 3 → ZMod 2)) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.ker (labelSum u)) := by
  have h := (labelSum u).finrank_range_add_finrank_ker
  have hr := (LinearMap.range (labelSum u)).finrank_le
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h hr
  omega

/-- A binary vector is the incidence vector of the positions where its value is one. -/
theorem exists_indicator {ι : Type*} [Finite ι] (x : ι → ZMod 2) :
    ∃ E : Finset ι, (E : Set ι).indicator (1 : ι → ZMod 2) = x := by
  classical
  let := Fintype.ofFinite ι
  refine ⟨univ.filter (fun i => x i = 1), ?_⟩
  funext i
  rcases binary_scalar (x i) with h | h <;> simp [h]

/-- Nonzero vectors in the label-sum kernel are precisely nonempty zero-set
incidence vectors, as used in the middle sentence of Remark 4.2. -/
theorem zeroSet_of_kernel_vector (u : Fin 5 → (Fin 3 → ZMod 2))
    (x : Fin 5 → ZMod 2) (hx : labelSum u x = 0) (hx0 : x ≠ 0) :
    ∃ E, IsZeroSet u E ∧ (E : Set (Fin 5)).indicator (1 : Fin 5 → ZMod 2) = x := by
  classical
  obtain ⟨E, hE⟩ := exists_indicator x
  refine ⟨E, ⟨?_, ?_⟩, hE⟩
  · apply nonempty_iff_ne_empty.2
    intro h
    apply hx0
    funext i
    simpa [h] using congrFun hE.symm i
  · have hsum : labelSum u ((E : Set (Fin 5)).indicator 1) = ∑ i ∈ E, u i := by
      change ∑ i, ((E : Set (Fin 5)).indicator (1 : Fin 5 → ZMod 2) i) • u i = _
      simp [Set.indicator_apply]
    rw [← hsum, hE]
    exact hx

/-- **Remark 4.2, Section 4, upper bound.** Two independent nonzero kernel
vectors and their sum contradict the additivity of the linear part of a separator. -/
theorem not_hasSeparator_five (u : Fin 5 → (Fin 3 → ZMod 2)) :
    ¬ HasSeparator (ZMod 2) u 1 := by
  classical
  rintro ⟨P, hdeg, h0, hzero⟩
  let ℓ := affineLinearPart P hdeg
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (two_le_finrank_ker u)
  let x : Fin 5 → ZMod 2 := v 0
  let y : Fin 5 → ZMod 2 := v 1
  have hx0 : x ≠ 0 := fun h => hv.ne_zero 0 (Subtype.ext h)
  have hy0 : y ≠ 0 := fun h => hv.ne_zero 1 (Subtype.ext h)
  have hxy : x ≠ y := fun h => (by decide : (0 : Fin 2) ≠ 1) (hv.injective (Subtype.ext h))
  have hxy0 : x + y ≠ 0 := by
    intro h
    apply hxy
    rw [add_eq_zero_iff_eq_neg] at h
    funext i
    simpa only [Pi.neg_apply, ZMod.neg_eq_self_mod_two] using congrFun h i
  have values : ∀ z : Fin 5 → ZMod 2, labelSum u z = 0 → z ≠ 0 → ℓ z = 1 := by
    intro z hz hz0
    obtain ⟨E, hE, hEz⟩ := zeroSet_of_kernel_vector u z hz hz0
    have he := hzero E hE
    rw [hEz] at he
    change eval z P - eval 0 P = 1
    rw [he, h0]
    decide
  have hx := values x (v 0).property hx0
  have hy := values y (v 1).property hy0
  have hs := values (x + y) (by rw [map_add, (v 0).property, (v 1).property, add_zero]) hxy0
  have ha := ℓ.map_add x y
  rw [hx, hy, hs] at ha
  exact (by decide : (1 : ZMod 2) ≠ 1 + 1) ha

/-- The four-term sequence `e₁ e₂ e₃²` in the last sentence of Remark 4.2. -/
def fourTermSequence : Fin 4 → (Fin 3 → ZMod 2) :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![0, 0, 1]]

/-- The only nonempty zero set of the four-term witness is its repeated pair. -/
theorem fourTermSequence_zeroSet : ∀ E : Finset (Fin 4),
    IsZeroSet fourTermSequence E ↔ E = {2, 3} := by
  unfold IsZeroSet
  decide +kernel

/-- **Remark 4.2, Section 4, lower bound.** The polynomial `1 + z₃` separates
`e₁ e₂ e₃²`; Lean's coordinate `2` is the paper's third position. -/
theorem fourTermSequence_separator :
    IsSeparator (ZMod 2) fourTermSequence 1 (1 + X 2) := by
  refine ⟨(totalDegree_add _ _).trans ?_, by simp, ?_⟩
  · simp
  · intro E hE
    rw [(fourTermSequence_zeroSet E).1 hE]
    norm_num [Set.indicator_apply]
    decide

end CharacteristicTwo

/-- **Remark 4.2, Section 4.** In characteristic two the affine threshold is
`κ₁(C₂³; F₂) = 5`, by rank-nullity and the four-term separating example. -/
theorem kappa_cube_two_zmod_two_one : kappa (Fin 3 → ZMod 2) (ZMod 2) 1 = 5 := by
  apply (kappa_eq_iff _ _ 1 5).2
  refine ⟨CharacteristicTwo.not_hasSeparator_five, ?_⟩
  intro N hN
  exact Sharpness.exists_hasSeparator_of_le (ZMod 2) (by omega : N ≤ 4)
    ⟨CharacteristicTwo.fourTermSequence, 1 + MvPolynomial.X 2,
      CharacteristicTwo.fourTermSequence_separator⟩

end DavenportProject
