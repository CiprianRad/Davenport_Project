/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Bases.CubeFour.Codes
public import DavenportProject.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import DavenportProject.Bases.CubeThree.Normalize
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Normal form over `C_4^3`

`exists_isNormal`: an injective additive map sends support terms of maximal multiplicity to the
standard basis vectors (or the sequence avoids them). `exists_sortedCodes` then sorts the
positions and produces the normalized code list that the enumeration of Lemma 5.3 covers.
-/

public section

namespace DavenportProject.CubeFour

open Finset Matrix DavenportCompute

/-!
## Linear normalization for Lemma 5.3

Every sequence `u` over `G = (ZMod 4)^3` is carried into the normal form `IsNormal` of the
enumeration by an injective additive endomorphism `φ` of `G` (`exists_isNormal`).

* A matrix `M` over a commutative ring with unit determinant gives the injective additive map
  `v ↦ v ᵥ* M⁻¹`, which sends the row `M j` to `Pi.single j 1` (`exists_addHom_of_isUnit`).
* An injective additive `φ` keeps multiplicities (`mult_comp`), and the predicates `P1g`,
  `P2g`, `P3g` are pulled back along `φ` as soon as `φ` fixes `e₀` (for `P2g`), resp. `e₀` and
  `e₁` (for `P3g`), because they are defined through `2 • x`.
* The normalization proceeds in three steps (`exists_normCond`). In step `k`, if some term
  satisfies `P(k+1)g`, a value `b` of maximal multiplicity among those terms is sent to `e_k` by
  a map fixing `e₀, …, e_(k-1)` (`P1g.exists_addHom`, `P2g.exists_addHom`, `P3g.exists_addHom`):
  the rows `e₀, …, e_(k-1), b` are completed by standard basis vectors to a matrix whose
  determinant is `±` an odd coordinate of `b`, hence a unit. The conditions established by the
  earlier steps survive the later maps (`NormCond.comp`).
-/

/-! ### Automorphisms from matrices -/

/-- A matrix with unit determinant gives an injective additive map sending its rows to the
standard basis. -/
theorem exists_addHom_of_isUnit {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M : Matrix n n R) (h : IsUnit M.det) :
    ∃ φ : (n → R) →+ (n → R), Function.Injective φ ∧ ∀ j, φ (M.row j) = Pi.single j 1 := by
  refine ⟨AddMonoidHom.mk' (fun v => v ᵥ* M⁻¹) (fun v w => add_vecMul M⁻¹ v w),
    fun v w hvw => ?_, fun j => ?_⟩
  · have := congrArg (fun z => z ᵥ* M) hvw
    simpa only [AddMonoidHom.mk'_apply, vecMul_vecMul, nonsing_inv_mul M h, vecMul_one]
      using this
  · rw [AddMonoidHom.mk'_apply, ← single_one_vecMul j M, vecMul_vecMul, mul_nonsing_inv M h,
      vecMul_one]

/-! ### Determinants of completed matrices -/

section Det

variable (b : Fin 3 → ZMod 4)

theorem det_b_e₁_e₂ : det (of ![b, Pi.single 1 1, Pi.single 2 1]) = b 0 := by
  simp [det_fin_three]

theorem det_b_e₀_e₂ : det (of ![b, Pi.single 0 1, Pi.single 2 1]) = -b 1 := by
  simp [det_fin_three]

theorem det_b_e₀_e₁ : det (of ![b, Pi.single 0 1, Pi.single 1 1]) = b 2 := by
  simp [det_fin_three]

theorem det_e₀_b_e₂ : det (of ![Pi.single 0 1, b, Pi.single 2 1]) = b 1 := by
  simp [det_fin_three]

theorem det_e₀_b_e₁ : det (of ![Pi.single 0 1, b, Pi.single 1 1]) = -b 2 := by
  simp [det_fin_three]

theorem det_e₀_e₁_b : det (of ![Pi.single 0 1, Pi.single 1 1, b]) = b 2 := by
  simp [det_fin_three]

end Det

/-! ### The predicates in coordinates -/

theorem two_smul_apply (x : Fin 3 → ZMod 4) (k : Fin 3) : (2 • x) k = 2 * x k := by
  simp [nsmul_eq_mul]

theorem two_mul_eq_zero_of_mul_self_ne_one : ∀ a : ZMod 4, a * a ≠ 1 → 2 * a = 0 := by
  decide

theorem two_mul_eq_zero_or_eq_two : ∀ a : ZMod 4, 2 * a = 0 ∨ 2 * a = 2 := by
  decide

theorem isUnit_of_mul_self {a : ZMod 4} (h : a * a = 1) : IsUnit a :=
  IsUnit.of_mul_eq_one a h

theorem isUnit_neg_of_mul_self {a : ZMod 4} (h : a * a = 1) : IsUnit (-a) :=
  IsUnit.of_mul_eq_one (-a) (by rw [neg_mul_neg, h])

/-- A term satisfying `P1g` has an odd coordinate. -/
theorem P1g.mul_self_eq_one {x : Fin 3 → ZMod 4} (h : P1g x) :
    x 0 * x 0 = 1 ∨ x 1 * x 1 = 1 ∨ x 2 * x 2 = 1 := by
  by_contra! hx
  obtain ⟨h0, h1, h2⟩ := hx
  refine h (funext fun k => ?_)
  rw [two_smul_apply, Pi.zero_apply]
  fin_cases k
  · exact two_mul_eq_zero_of_mul_self_ne_one _ h0
  · exact two_mul_eq_zero_of_mul_self_ne_one _ h1
  · exact two_mul_eq_zero_of_mul_self_ne_one _ h2

/-- A term satisfying `P2g` has an odd coordinate `x₁` or `x₂`. -/
theorem P2g.mul_self_eq_one {x : Fin 3 → ZMod 4} (h : P2g x) :
    x 1 * x 1 = 1 ∨ x 2 * x 2 = 1 := by
  by_contra! hx
  obtain ⟨h1, h2⟩ := hx
  have h1 := two_mul_eq_zero_of_mul_self_ne_one _ h1
  have h2 := two_mul_eq_zero_of_mul_self_ne_one _ h2
  rcases two_mul_eq_zero_or_eq_two (x 0) with h0 | h0
  · refine h.1 (funext fun k => ?_)
    fin_cases k <;> simpa [two_smul_apply]
  · refine h.2 (funext fun k => ?_)
    fin_cases k <;> simpa [two_smul_apply]

/-- A term satisfying `P3g` has an odd coordinate `x₂`. -/
theorem P3g.mul_self_eq_one {x : Fin 3 → ZMod 4} (h : P3g x) : x 2 * x 2 = 1 := by
  by_contra hx
  have h2 := two_mul_eq_zero_of_mul_self_ne_one _ hx
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  rcases two_mul_eq_zero_or_eq_two (x 0) with h0 | h0 <;>
    rcases two_mul_eq_zero_or_eq_two (x 1) with h1 | h1
  · exact h₁ (funext fun k => by fin_cases k <;> simpa [two_smul_apply])
  · exact h₃ (funext fun k => by fin_cases k <;> simpa [two_smul_apply])
  · exact h₂ (funext fun k => by fin_cases k <;> simpa [two_smul_apply])
  · exact h₄ (funext fun k => by fin_cases k <;> simpa [two_smul_apply])

/-! ### Pulling back the predicates -/

/-- `P1g` is pulled back along any additive endomorphism. -/
theorem P1g.of_map (φ : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4)) {x : Fin 3 → ZMod 4}
    (h : P1g (φ x)) : P1g x := fun hx => h (by rw [← map_nsmul, hx, map_zero])

/-- `P2g` is pulled back along any additive endomorphism fixing `e₀`. -/
theorem P2g.of_map (φ : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4))
    (h₀ : φ (Pi.single 0 1) = Pi.single 0 1) {x : Fin 3 → ZMod 4} (h : P2g (φ x)) : P2g x :=
  ⟨fun hx => h.1 (by rw [← map_nsmul, hx, map_zero]),
    fun hx => h.2 (by rw [← map_nsmul, hx, map_nsmul, h₀])⟩

/-- `P3g` is pulled back along any additive endomorphism fixing `e₀` and `e₁`. -/
theorem P3g.of_map (φ : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4))
    (h₀ : φ (Pi.single 0 1) = Pi.single 0 1) (h₁ : φ (Pi.single 1 1) = Pi.single 1 1)
    {x : Fin 3 → ZMod 4} (h : P3g (φ x)) : P3g x :=
  ⟨fun hx => h.1 (by rw [← map_nsmul, hx, map_zero]),
    fun hx => h.2.1 (by rw [← map_nsmul, hx, map_nsmul, h₀]),
    fun hx => h.2.2.1 (by rw [← map_nsmul, hx, map_nsmul, h₁]),
    fun hx => h.2.2.2 (by rw [← map_nsmul, hx, map_nsmul, map_add, h₀, h₁])⟩

/-! ### The three normalizing maps -/

/-- A term satisfying `P1g` is sent to `e₀` by an injective additive map. -/
theorem P1g.exists_addHom {b : Fin 3 → ZMod 4} (hb : P1g b) :
    ∃ φ : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4), Function.Injective φ ∧
      φ b = Pi.single 0 1 := by
  rcases hb.mul_self_eq_one with h | h | h
  · obtain ⟨φ, hφ, hM⟩ := exists_addHom_of_isUnit _
      (by rw [det_b_e₁_e₂]; exact isUnit_of_mul_self h)
    exact ⟨φ, hφ, hM 0⟩
  · obtain ⟨φ, hφ, hM⟩ := exists_addHom_of_isUnit _
      (by rw [det_b_e₀_e₂]; exact isUnit_neg_of_mul_self h)
    exact ⟨φ, hφ, hM 0⟩
  · obtain ⟨φ, hφ, hM⟩ := exists_addHom_of_isUnit _
      (by rw [det_b_e₀_e₁]; exact isUnit_of_mul_self h)
    exact ⟨φ, hφ, hM 0⟩

/-- A term satisfying `P2g` is sent to `e₁` by an injective additive map fixing `e₀`. -/
theorem P2g.exists_addHom {b : Fin 3 → ZMod 4} (hb : P2g b) :
    ∃ φ : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4), Function.Injective φ ∧
      φ (Pi.single 0 1) = Pi.single 0 1 ∧ φ b = Pi.single 1 1 := by
  rcases hb.mul_self_eq_one with h | h
  · obtain ⟨φ, hφ, hM⟩ := exists_addHom_of_isUnit _
      (by rw [det_e₀_b_e₂]; exact isUnit_of_mul_self h)
    exact ⟨φ, hφ, hM 0, hM 1⟩
  · obtain ⟨φ, hφ, hM⟩ := exists_addHom_of_isUnit _
      (by rw [det_e₀_b_e₁]; exact isUnit_neg_of_mul_self h)
    exact ⟨φ, hφ, hM 0, hM 1⟩

/-- A term satisfying `P3g` is sent to `e₂` by an injective additive map fixing `e₀, e₁`. -/
theorem P3g.exists_addHom {b : Fin 3 → ZMod 4} (hb : P3g b) :
    ∃ φ : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4), Function.Injective φ ∧
      φ (Pi.single 0 1) = Pi.single 0 1 ∧ φ (Pi.single 1 1) = Pi.single 1 1 ∧
        φ b = Pi.single 2 1 := by
  obtain ⟨φ, hφ, hM⟩ := exists_addHom_of_isUnit _
    (by rw [det_e₀_e₁_b]; exact isUnit_of_mul_self hb.mul_self_eq_one)
  exact ⟨φ, hφ, hM 0, hM 1, hM 2⟩

section Normalization

variable {ι : Type*} [Fintype ι]

/-! ### Multiplicities -/

/-- An injective map does not change multiplicities. -/
theorem mult_comp {φ : (Fin 3 → ZMod 4) → (Fin 3 → ZMod 4)} (hφ : Function.Injective φ)
    (v : ι → (Fin 3 → ZMod 4)) (x : Fin 3 → ZMod 4) :
    mult (fun i => φ (v i)) (φ x) = mult v x := by
  unfold mult
  simp only [hφ.eq_iff]

/-- A bound on the multiplicity of `x` need only be checked when `x` occurs. -/
theorem mult_le_of_forall {v : ι → (Fin 3 → ZMod 4)} {x : Fin 3 → ZMod 4} {n : ℕ}
    (h : ∀ i, v i = x → mult v x ≤ n) : mult v x ≤ n := by
  by_cases hx : ∃ i, v i = x
  · obtain ⟨i, hi⟩ := hx
    exact h i hi
  · have : mult v x = 0 := by
      unfold mult
      simpa using hx
    omega

/-! ### The normalization -/

/-- The pair of conditions of `IsNormal` attached to a predicate `P` and a vector `e`: `e`
occurs in `v` unless no term satisfies `P`, and no value satisfying `P` occurs more often than
`e`. -/
def NormCond (P : (Fin 3 → ZMod 4) → Prop) (e : Fin 3 → ZMod 4) (v : ι → (Fin 3 → ZMod 4)) :
    Prop :=
  ((∃ i, v i = e) ∨ ∀ i, ¬ P (v i)) ∧ ∀ x, P x → mult v x ≤ mult v e

/-- `NormCond P e` survives an injective additive map fixing `e` along which `P` is pulled back. -/
theorem NormCond.comp {P : (Fin 3 → ZMod 4) → Prop} {e : Fin 3 → ZMod 4}
    {v : ι → (Fin 3 → ZMod 4)} (h : NormCond P e v) {φ : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4)}
    (hφ : Function.Injective φ) (he : φ e = e) (hP : ∀ x, P (φ x) → P x) :
    NormCond P e (fun i => φ (v i)) := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, fun x hx => ?_⟩
  · rcases h₁ with ⟨i, hi⟩ | h₁
    · exact Or.inl ⟨i, (congrArg φ hi).trans he⟩
    · exact Or.inr fun i hi => h₁ i (hP _ hi)
  · obtain ⟨y, rfl⟩ := Finite.surjective_of_injective hφ x
    rw [mult_comp hφ, ← he, mult_comp hφ]
    exact h₂ y (hP y hx)

/-- One normalization step: if every value satisfying `P` is sent to `e` by a map in a class
`Q` of injective additive maps containing the identity and along which `P` is pulled back, then
some map of `Q` establishes `NormCond P e`. The map is applied to a value of maximal multiplicity
among the terms satisfying `P`. -/
theorem exists_normCond (P : (Fin 3 → ZMod 4) → Prop) (e : Fin 3 → ZMod 4)
    (Q : ((Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4)) → Prop) (hid : Q (AddMonoidHom.id _))
    (hQ : ∀ φ, Q φ → Function.Injective φ ∧ ∀ x, P (φ x) → P x)
    (hb : ∀ b, P b → ∃ φ, Q φ ∧ φ b = e) (v : ι → (Fin 3 → ZMod 4)) :
    ∃ φ, Q φ ∧ NormCond P e (fun i => φ (v i)) := by
  classical
  by_cases hP : ∃ i, P (v i)
  · obtain ⟨i, hi⟩ := hP
    obtain ⟨i₀, hi₀, hmax⟩ := exists_max_image {i | P (v i)} (fun i => mult v (v i))
      ⟨i, mem_filter.2 ⟨mem_univ i, hi⟩⟩
    obtain ⟨φ, hQφ, hφb⟩ := hb (v i₀) (mem_filter.1 hi₀).2
    obtain ⟨hφ, hφP⟩ := hQ φ hQφ
    refine ⟨φ, hQφ, Or.inl ⟨i₀, hφb⟩, fun x hx => ?_⟩
    obtain ⟨y, rfl⟩ := Finite.surjective_of_injective hφ x
    rw [mult_comp hφ, ← hφb, mult_comp hφ]
    refine mult_le_of_forall fun j hj => ?_
    rw [← hj]
    exact hmax j (mem_filter.2 ⟨mem_univ j, hj ▸ hφP y hx⟩)
  · refine ⟨AddMonoidHom.id _, hid, Or.inr (not_exists.1 hP),
      fun x hx => mult_le_of_forall fun i hi => ?_⟩
    rw [AddMonoidHom.id_apply] at hi
    exact (hP ⟨i, hi ▸ hx⟩).elim

/-- Every sequence over `(ZMod 4)^3` is carried into the normal form `IsNormal` by an
injective additive endomorphism. -/
theorem exists_isNormal {ι : Type*} [Fintype ι] (u : ι → (Fin 3 → ZMod 4)) :
    ∃ φ : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4), Function.Injective φ ∧
      IsNormal (fun i => φ (u i)) := by
  obtain ⟨φ₁, hφ₁, hC₁⟩ := exists_normCond P1g (Pi.single 0 1) (fun φ => Function.Injective φ)
    Function.injective_id (fun φ hφ => ⟨hφ, fun _ => P1g.of_map φ⟩)
    (fun _ hb => hb.exists_addHom) u
  obtain ⟨φ₂, ⟨hφ₂, h₂₀⟩, hC₂⟩ := exists_normCond P2g (Pi.single 1 1)
    (fun φ => Function.Injective φ ∧ φ (Pi.single 0 1) = Pi.single 0 1)
    ⟨Function.injective_id, rfl⟩ (fun φ hφ => ⟨hφ.1, fun _ => P2g.of_map φ hφ.2⟩)
    (fun _ hb => let ⟨φ, hφ, h₀, h⟩ := hb.exists_addHom; ⟨φ, ⟨hφ, h₀⟩, h⟩)
    (fun i => φ₁ (u i))
  obtain ⟨φ₃, ⟨hφ₃, h₃₀, h₃₁⟩, hC₃⟩ := exists_normCond P3g (Pi.single 2 1)
    (fun φ => Function.Injective φ ∧ φ (Pi.single 0 1) = Pi.single 0 1 ∧
      φ (Pi.single 1 1) = Pi.single 1 1)
    ⟨Function.injective_id, rfl, rfl⟩ (fun φ hφ => ⟨hφ.1, fun _ => P3g.of_map φ hφ.2.1 hφ.2.2⟩)
    (fun _ hb => let ⟨φ, hφ, h₀, h₁, h⟩ := hb.exists_addHom; ⟨φ, ⟨hφ, h₀, h₁⟩, h⟩)
    (fun i => φ₂ (φ₁ (u i)))
  have hC₁' := (hC₁.comp hφ₂ h₂₀ fun _ => P1g.of_map φ₂).comp hφ₃ h₃₀ fun _ => P1g.of_map φ₃
  have hC₂' := hC₂.comp hφ₃ h₃₁ fun _ => P2g.of_map φ₃ h₃₀
  exact ⟨φ₃.comp (φ₂.comp φ₁), hφ₃.comp (hφ₂.comp hφ₁),
    hC₁'.1, hC₁'.2, hC₂'.1, hC₂'.2, hC₃.1, hC₃.2⟩

end Normalization

/-!
## From a short-zero-free sequence over `C_4^3` to a normalized sorted code list

`exists_sortedCodes`: for a sequence `u` over `(ZMod 4)^3` without zero sets of size at most
four, an injective additive map `φ` (`exists_isNormal`) followed by a reindexing `σ` that sorts the
codes gives a code sequence `c` with `dec 4 (c k) = φ (u (σ k))`, whose list `List.ofFn c`
is sorted, has entries in `[1, 64)`, is short-zero-free (`ListSZF`), satisfies the guards of the
enumeration (`Guards`) and the multiplicity normalization (`n3cond`).

`hasIncidenceIdentity_of_sortedCodes` moves an identity of `dec 4 ∘ c` back to `u`.
-/

/-- The count of `a` in `List.ofFn c` is the number of positions where `c` takes the value `a`. -/
theorem count_ofFn {N : ℕ} (c : Fin N → ℕ) (a : ℕ) :
    (List.ofFn c).count a = #{k | c k = a} := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, ih, Fin.card_filter_univ_succ']
    by_cases h : c 0 = a <;> simp [h, add_comm]

theorem enc_ne_zero_of_szf {ι : Type*} {u : ι → (Fin 3 → ZMod 4)}
    (hu : ∀ E : Finset ι, IsZeroSet u E → 4 < #E) (i : ι) : enc 4 (u i) ≠ 0 := by
  intro h
  have h0 : u i = 0 := by rw [← dec_enc (u i), h, dec_zero]
  have := hu {i} ⟨⟨i, mem_singleton_self i⟩, by simp [h0]⟩
  simp at this

/-- A short-zero-free sequence becomes a normalized sorted code list (see the section docstring). -/
theorem exists_sortedCodes {N : ℕ} (u : Fin N → (Fin 3 → ZMod 4))
    (hu : ∀ E : Finset (Fin N), IsZeroSet u E → 4 < #E) :
    ∃ φ : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4), Function.Injective φ ∧
      ∃ (σ : Equiv.Perm (Fin N)) (c : Fin N → ℕ), (∀ k, dec 4 (c k) = φ (u (σ k))) ∧
        (List.ofFn c).Pairwise (· ≤ ·) ∧ (∀ y ∈ List.ofFn c, 1 ≤ y ∧ y < 64) ∧
        ListSZF (List.ofFn c) ∧ Guards (List.ofFn c) ∧ n3cond (List.ofFn c).reverse = true := by
  classical
  obtain ⟨φ, hφ, hnorm⟩ := exists_isNormal u
  set v : Fin N → (Fin 3 → ZMod 4) := fun i => φ (u i) with hv
  have hvszf : ∀ E : Finset (Fin N), IsZeroSet v E → 4 < #E := fun E hE =>
    hu E ((CubeThree.Identity.isZeroSet_comp_iff φ hφ u E).1 hE)
  set f : Fin N → ℕ := fun i => enc 4 (v i) with hf
  set σ := Tuple.sort f
  set c : Fin N → ℕ := fun k => f (σ k) with hc
  have hmono : Monotone c := Tuple.monotone_sort f
  have hdec : ∀ k, dec 4 (c k) = v (σ k) := fun k => dec_enc _
  have hlt : ∀ k, c k < 64 := fun k => enc_lt (v (σ k))
  have hmem : ∀ {y}, y ∈ List.ofFn c ↔ ∃ k, c k = y := by
    intro y; simp [List.mem_ofFn]
  -- counts in the code list are multiplicities in `v`
  have hcount : ∀ x, (List.ofFn c).count (enc 4 x) = mult v x := by
    intro x
    rw [count_ofFn, mult]
    have : #{k | c k = enc 4 x} = #{k | v (σ k) = x} := by
      congr 1
      ext k
      simp only [mem_filter, mem_univ, true_and, hc, hf]
      exact ⟨fun h => by rw [← dec_enc (v (σ k)), h, dec_enc], fun h => by rw [h]⟩
    rw [this]
    exact card_bij (fun k _ => σ k) (by simp) (fun a _ b _ h => σ.injective h)
      (fun i hi => ⟨σ.symm i, by simpa using hi, by simp⟩)
  refine ⟨φ, hφ, σ, c, hdec, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact hmono hij.le
  · intro y hy
    obtain ⟨k, rfl⟩ := hmem.1 hy
    exact ⟨Nat.one_le_iff_ne_zero.2 (enc_ne_zero_of_szf hvszf (σ k)), hlt k⟩
  · refine listSZF_ofFn c hlt fun E hE => ?_
    have hE' : IsZeroSet (fun k => v (σ k)) E := by simpa only [hdec] using hE
    have := hvszf _ ((isZeroSet_map_equiv v σ E).2 hE')
    simpa using this
  · obtain ⟨hA, -, hB, -, hC, -⟩ := hnorm
    have hguard : ∀ (e : Fin 3 → ZMod 4) (P : (Fin 3 → ZMod 4) → Prop) (Q : ℕ → Bool),
        (∀ x, Q (enc 4 x) = true ↔ P x) → ((∃ i, v i = e) ∨ ∀ i, ¬ P (v i)) →
        enc 4 e ∈ List.ofFn c ∨ ∀ y ∈ List.ofFn c, Q y = false := by
      intro e P Q hQ h
      rcases h with ⟨i, hi⟩ | h
      · refine Or.inl (hmem.2 ⟨σ.symm i, ?_⟩)
        simp [hc, hf, hi]
      · refine Or.inr fun y hy => ?_
        obtain ⟨k, rfl⟩ := hmem.1 hy
        have hk := h (σ k)
        rw [← hQ] at hk
        simpa [hc, hf] using hk
    refine ⟨?_, ?_, ?_⟩
    · simpa [enc_e0] using hguard _ _ P1 P1_enc hA
    · simpa [enc_e1] using hguard _ _ P2 P2_enc hB
    · simpa [enc_e2] using hguard _ _ P3 P3_enc hC
  · obtain ⟨-, hA, -, hB, -, hC⟩ := hnorm
    simp only [n3cond, List.count_reverse, List.all_eq_true, List.mem_reverse, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    have h1 : (List.ofFn c).count 1 = mult v (Pi.single 0 1) := by
      simpa [enc_e0] using hcount (Pi.single 0 1)
    have h4 : (List.ofFn c).count 4 = mult v (Pi.single 1 1) := by
      simpa [enc_e1] using hcount (Pi.single 1 1)
    have h16 : (List.ofFn c).count 16 = mult v (Pi.single 2 1) := by
      simpa [enc_e2] using hcount (Pi.single 2 1)
    intro y hy
    obtain ⟨k, hk⟩ := hmem.1 hy
    obtain ⟨x, rfl⟩ : ∃ x, y = enc 4 x := ⟨dec 4 y, (enc_dec (hk ▸ hlt k)).symm⟩
    rw [hcount, h1, h4, h16]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_cases h : P1 (enc 4 x) = true
      · exact Or.inr (hA _ ((P1_enc _).1 h))
      · exact Or.inl (by simpa using h)
    · by_cases h : P2 (enc 4 x) = true
      · exact Or.inr (hB _ ((P2_enc _).1 h))
      · exact Or.inl (by simpa using h)
    · by_cases h : P3 (enc 4 x) = true
      · exact Or.inr (hC _ ((P3_enc _).1 h))
      · exact Or.inl (by simpa using h)

/-- An identity of the code sequence moves back to the original sequence. -/
theorem hasIncidenceIdentity_of_sortedCodes {N t : ℕ} {u : Fin N → (Fin 3 → ZMod 4)}
    {φ : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4)} (hφ : Function.Injective φ)
    {σ : Equiv.Perm (Fin N)} {c : Fin N → ℕ} (hdec : ∀ k, dec 4 (c k) = φ (u (σ k)))
    (h : HasIncidenceIdentity ℤ (fun k => dec 4 (c k)) t) : HasIncidenceIdentity ℤ u t := by
  refine CubeThree.Identity.hasIncidenceIdentity_of_comp φ hφ ?_
  have h' := hasIncidenceIdentity_comp_equiv (fun k => dec 4 (c k)) σ.symm h
  simpa [hdec] using h'

end DavenportProject.CubeFour
