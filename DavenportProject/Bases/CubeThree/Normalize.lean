/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

/-!
# Linear normalization over `C_3^3`

Linear normalization for Lemma 5.1(1). An injective additive endomorphism `φ` of `G` does not
change the zero sets of a sequence, so `u` and `φ ∘ u` have the same incidence identities
(`hasIncidenceIdentity_of_comp`).

For a matrix `M` over `ZMod 3` with `det M ≠ 0`, `v ↦ v ᵥ* (det M • adj M)` is such a
map, and it sends the row `M j` to the basis vector `Pi.single j 1` (`exists_addHom_of_det`).
Two linearly independent vectors `x, y` are completed to such a matrix by a basis vector,
because their cross product is nonzero (`exists_det_ne_zero`).
-/

public section

namespace DavenportProject.CubeThree.Identity

open Matrix

variable {G : Type*} [AddCommGroup G] {ι : Type*}

theorem isZeroSet_comp_iff (φ : G →+ G) (hφ : Function.Injective φ) (u : ι → G)
    (E : Finset ι) : IsZeroSet (fun i => φ (u i)) E ↔ IsZeroSet u E := by
  unfold IsZeroSet
  refine and_congr_right fun _ => ?_
  rw [← map_sum]
  exact ⟨fun h => hφ (h.trans (map_zero φ).symm), fun h => by rw [h, map_zero]⟩

/-- Incidence identities transport back along an injective additive endomorphism. -/
theorem hasIncidenceIdentity_of_comp [Fintype ι] {R : Type*} [CommRing R] {t : ℕ}
    (φ : G →+ G) (hφ : Function.Injective φ) {u : ι → G}
    (h : HasIncidenceIdentity R (fun i => φ (u i)) t) : HasIncidenceIdentity R u t := by
  have hZ : zeroSets (fun i => φ (u i)) = zeroSets u := by
    ext E
    rw [mem_zeroSets, mem_zeroSets, isZeroSet_comp_iff φ hφ]
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  unfold IsIncidenceIdentity at hc ⊢
  rwa [hZ] at hc

theorem mul_self_of_ne_zero : ∀ a : ZMod 3, a ≠ 0 → a * a = 1 := by decide

/-- A matrix with nonzero determinant over `ZMod 3` gives an injective additive map sending
its rows to the standard basis. -/
theorem exists_addHom_of_det (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) (h : M.det ≠ 0) :
    ∃ φ : (Fin 3 → ZMod 3) →+ (Fin 3 → ZMod 3), Function.Injective φ ∧
      ∀ j, φ (M j) = Pi.single j 1 := by
  set N := M.det • M.adjugate
  have hNM : N * M = 1 := by
    rw [smul_mul_assoc, adjugate_mul, smul_smul, mul_self_of_ne_zero _ h, one_smul]
  have hMN : M * N = 1 := by
    rw [mul_smul_comm, mul_adjugate, smul_smul, mul_self_of_ne_zero _ h, one_smul]
  refine ⟨AddMonoidHom.mk' (fun v => v ᵥ* N) (fun v w => add_vecMul N v w),
    fun v w hvw => ?_, fun j => ?_⟩
  · have := congrArg (fun z => z ᵥ* M) hvw
    simpa only [AddMonoidHom.mk'_apply, vecMul_vecMul, hNM, vecMul_one] using this
  · change M j ᵥ* N = _
    have hj : Pi.single j 1 ᵥ* M = M j := single_one_vecMul j M
    rw [← hj, vecMul_vecMul, hMN, vecMul_one]

theorem det_single (x y : Fin 3 → ZMod 3) (k : Fin 3) :
    Matrix.det ![x, y, Pi.single k 1] = (x ⨯₃ y) k := by
  rw [← triple_product_eq_det, triple_product_permutation, triple_product_permutation,
    single_one_dotProduct]

theorem two_smul_eq_neg (x : Fin 3 → ZMod 3) : (2 : ZMod 3) • x = -x := by
  ext i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  generalize x i = a
  revert a
  decide

/-- Two independent vectors are completed by a standard basis vector. -/
theorem exists_det_ne_zero {x y : Fin 3 → ZMod 3} (hx : x ≠ 0) (hy0 : y ≠ 0) (hyx : x ≠ y)
    (hyn : -x ≠ y) : ∃ k : Fin 3, Matrix.det ![x, y, Pi.single k 1] ≠ 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hli : LinearIndependent (ZMod 3) ![x, y] := by
    refine (LinearIndependent.pair_iff' (K := ZMod 3) hx).2 fun a => ?_
    fin_cases a
    · change (0 : ZMod 3) • x ≠ y
      rw [zero_smul]
      exact Ne.symm hy0
    · change (1 : ZMod 3) • x ≠ y
      rw [one_smul]
      exact hyx
    · change (2 : ZMod 3) • x ≠ y
      rw [two_smul_eq_neg]
      exact hyn
  have hc := (crossProduct_ne_zero_iff_linearIndependent (F := ZMod 3)).2 hli
  by_contra hall
  simp only [not_exists, not_not] at hall
  exact hc (funext fun k => by rw [← det_single]; exact hall k)

theorem det_e₁_e₂ (w : Fin 3 → ZMod 3) :
    Matrix.det ![Pi.single 0 1, Pi.single 1 1, w] = w 2 := by
  rw [← triple_product_eq_det, single_one_dotProduct, cross_apply]
  simp

end DavenportProject.CubeThree.Identity
