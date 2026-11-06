/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George C. Rad
-/
module

public import DavenportProject.Defs
public import Mathlib.Data.ZMod.Basic
import DavenportProject.Bases.Basic
import DavenportProject.Bases.CubeTwo
import DavenportProject.Identities.Operations
import DavenportProject.Invariants

/-!
# Short zero sets over `C_4^3`

* `not_isShortZeroFree_cube_four`: `η(C_4^3) ≤ 22`, every twenty-two terms over `C_4^3` contain a
  zero set of size at most four (a result of Harborth, proved here by a double pigeonhole).
* The reductions used for Lemma 5.3 and Theorem B: a zero set of size at most four
  (`exists_isZeroSet_card_le_four_of_le_card`) and degree zero (`D(C_4^3) = 10`).
-/

/-!
## Proof of η(C_4^3) ≤ 22

Structural proof of `η(C_4^3) ≤ 22` (instead of the citation of Harborth 1973):

* `red : C_4^3 →+ C_2^3` is reduction mod 2; its kernel is `2G ≅ C_2^3`, an elementary abelian
  group (`add_self_eq_zero_of_red_eq_zero`).
* Among any eight terms, the `C_2^3` pigeonhole
  (`Bases.not_injective_and_ne_zero_of_le_card`) yields a *block*: one or two terms
  whose sum lies in `ker red` (`exists_block`).
* Twenty-two terms contain eight pairwise disjoint blocks (`exists_blocks`).
* The eight block sums lie in `ker red`, which `half` embeds into `C_2^3`; so one block sum is
  zero, or two block sums are equal and the union of the two blocks is a zero set. Either way
  this is a zero set of at most four terms, while `exp(C_4^3) ≥ 4`.
-/

@[expose] public section

namespace DavenportProject.CubeFour

open Finset DavenportProject DavenportProject.Bases

/-- Reduction mod 2, `C_4^3 → C_2^3`. -/
def red : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 2) :=
  (ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2)).toAddMonoidHom.compLeft (Fin 3)

/-- Halving on `{0, 2} ⊆ ZMod 4`. -/
def halfCoord (a : ZMod 4) : ZMod 2 := if a = 2 then 1 else 0

/-- Halving on `ker red = 2G`, coordinatewise. -/
def half (x : Fin 3 → ZMod 4) : Fin 3 → ZMod 2 := fun k => halfCoord (x k)

theorem red_apply (x : Fin 3 → ZMod 4) (k : Fin 3) :
    red x k = ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) (x k) := rfl

theorem coord_add_self :
    ∀ a : ZMod 4, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) a = 0 → a + a = 0 := by
  decide

theorem coord_eq_zero : ∀ a : ZMod 4, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) a = 0 →
    halfCoord a = 0 → a = 0 := by
  decide

theorem coord_inj : ∀ a b : ZMod 4, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) a = 0 →
    ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) b = 0 → halfCoord a = halfCoord b →
    a = b := by
  decide

/-- `ker red` has exponent two. -/
theorem add_self_eq_zero_of_red_eq_zero {x : Fin 3 → ZMod 4} (hx : red x = 0) : x + x = 0 := by
  funext k
  have h := congrFun hx k
  rw [red_apply] at h
  exact coord_add_self _ h

theorem eq_zero_of_half_eq_zero {x : Fin 3 → ZMod 4} (hx : red x = 0) (h : half x = 0) :
    x = 0 := by
  funext k
  have h1 := congrFun hx k
  rw [red_apply] at h1
  exact coord_eq_zero _ h1 (congrFun h k)

theorem eq_of_half_eq {x y : Fin 3 → ZMod 4} (hx : red x = 0) (hy : red y = 0)
    (h : half x = half y) : x = y := by
  funext k
  have h1 := congrFun hx k
  have h2 := congrFun hy k
  rw [red_apply] at h1 h2
  exact coord_inj _ _ h1 h2 (congrFun h k)

theorem four_le_exponent : 4 ≤ AddMonoid.exponent (Fin 3 → ZMod 4) := by
  have hne : AddMonoid.exponent (Fin 3 → ZMod 4) ≠ 0 := AddMonoid.exponent_ne_zero_of_finite
  have h := congrFun (AddMonoid.exponent_nsmul_eq_zero (fun _ : Fin 3 => (1 : ZMod 4))) 0
  simp only [Pi.smul_apply, nsmul_eq_mul, mul_one, Pi.zero_apply,
    ZMod.natCast_eq_zero_iff] at h
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h

variable {ι : Type*}

/-- Block lemma: among at least eight terms there are one or two whose sum lies in `ker red`. -/
theorem exists_block (u : ι → (Fin 3 → ZMod 4)) (S : Finset ι) (hS : 8 ≤ #S) :
    ∃ B ⊆ S, B.Nonempty ∧ #B ≤ 2 ∧ red (∑ i ∈ B, u i) = 0 := by
  let v : S → (Fin 3 → ZMod 2) := fun i => red (u i)
  obtain ⟨B, ⟨hne, hs⟩, hc⟩ :=
    exists_isZeroSet_card_le_two v (not_injective_and_ne_zero_of_le_card v (by simpa using hS))
  refine ⟨B.map (Function.Embedding.subtype _), ?_, hne.map, by simpa using hc, ?_⟩
  · intro i hi
    obtain ⟨a, -, rfl⟩ := mem_map.1 hi
    exact a.2
  · rw [map_sum, sum_map]
    exact hs

/-- From at least `2k + 8` positions one can choose `k + 1` pairwise disjoint blocks. -/
theorem exists_blocks (u : ι → (Fin 3 → ZMod 4)) (k : ℕ) :
    ∀ S : Finset ι, 2 * k + 8 ≤ #S → ∃ b : Fin (k + 1) → Finset ι,
      (∀ j, b j ⊆ S ∧ (b j).Nonempty ∧ #(b j) ≤ 2 ∧ red (∑ i ∈ b j, u i) = 0) ∧
      ∀ i j, i ≠ j → Disjoint (b i) (b j) := by
  classical
  induction k with
  | zero =>
    intro S hS
    obtain ⟨B, hB⟩ := exists_block u S (by omega)
    refine ⟨fun _ => B, fun _ => hB, fun i j h => absurd (Fin.ext ?_) h⟩
    have := i.2
    have := j.2
    omega
  | succ k ih =>
    intro S hS
    obtain ⟨B, hBS, hne, hc, hr⟩ := exists_block u S (by omega)
    have hcard : 2 * k + 8 ≤ #(S \ B) := by
      have := le_card_sdiff B S
      have := card_le_card hBS
      omega
    obtain ⟨b, hb, hd⟩ := ih (S \ B) hcard
    refine ⟨Fin.cons B b, fun j => ?_, fun i j hij => ?_⟩
    · induction j using Fin.cases with
      | zero => exact ⟨hBS, hne, hc, hr⟩
      | succ j =>
        obtain ⟨h1, h2, h3, h4⟩ := hb j
        exact ⟨h1.trans sdiff_subset, h2, h3, h4⟩
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => exact disjoint_sdiff.mono_right (hb j).1
      | succ i =>
        induction j using Fin.cases with
        | zero => exact (disjoint_sdiff.mono_right (hb i).1).symm
        | succ j => exact hd i j fun h => hij (by rw [h])

end DavenportProject.CubeFour

end

public section

namespace DavenportProject

open Finset DavenportProject DavenportProject.Bases
open DavenportProject.CubeFour

open Finset

/-- `η(C_4^3) ≤ 22` (Harborth 1973, cited in the paper and proved here): every twenty-two terms
over `C_4^3` contain a zero set of size at most `exp = 4`. -/
theorem not_isShortZeroFree_cube_four (u : Fin 22 → (Fin 3 → ZMod 4)) :
    ¬ IsShortZeroFree u := by
  intro h
  have key : ∀ E : Finset (Fin 22), E.Nonempty → #E ≤ 4 → ∑ i ∈ E, u i ≠ 0 :=
    fun E hE hc hs => absurd (h E ⟨hE, hs⟩) (by have := four_le_exponent; omega)
  obtain ⟨b, hb, hd⟩ := exists_blocks u 7 univ (by simp)
  have hpig := not_injective_and_ne_zero_of_le_card (fun j => half (∑ i ∈ b j, u i)) (by simp)
  rw [not_and_or] at hpig
  rcases hpig with hinj | hz
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    have hs := eq_of_half_eq (hb i).2.2.2 (hb j).2.2.2 hij
    refine key (b i ∪ b j) ((hb i).2.1.mono subset_union_left) ?_ ?_
    · rw [card_union_of_disjoint (hd i j hne)]
      have := (hb i).2.2.1
      have := (hb j).2.2.1
      omega
    · rw [sum_union (hd i j hne), hs]
      exact add_self_eq_zero_of_red_eq_zero (hb j).2.2.2
  · push Not at hz
    obtain ⟨j, hj⟩ := hz
    exact key (b j) (hb j).2.1 (by have := (hb j).2.2.1; omega)
      (eq_zero_of_half_eq_zero (hb j).2.2.2 hj)

end DavenportProject

end

/-!
## Short zero sets and degree zero over `C_4^3`
-/

public section

namespace DavenportProject.Bases

open Finset DavenportProject
open DavenportProject.Bases (exponent_fin_three_zmod)

/-- Twenty-two or more terms over `C_4^3` contain a zero set of size at most four. -/
theorem exists_isZeroSet_card_le_four_of_le_card {ι : Type*} [Fintype ι]
    (u : ι → (Fin 3 → ZMod 4)) (h : 22 ≤ Fintype.card ι) : ∃ B, IsZeroSet u B ∧ #B ≤ 4 := by
  have hu : ¬ IsShortZeroFree u := by
    intro hu
    have f : Fin 22 ↪ ι :=
      (Fin.castLEEmb h).trans (Fintype.equivFin ι).symm.toEmbedding
    exact not_isShortZeroFree_cube_four _ (isShortZeroFree_comp_embedding hu f)
  simp only [IsShortZeroFree, exponent_fin_three_zmod, not_forall, not_lt] at hu
  obtain ⟨B, hB, hc⟩ := hu
  exact ⟨B, hB, hc⟩

/-- Degree zero: ten terms over `C_4^3` have an integral `𝓘_0`-identity (`D(C_4^3) = 10`). -/
theorem hasIncidenceIdentity_zero_of_card_eq_ten {ι : Type*} [Fintype ι]
    (h : Fintype.card ι = 10) (u : ι → (Fin 3 → ZMod 4)) : HasIncidenceIdentity ℤ u 0 := by
  let e : ι ≃ Fin 10 := Fintype.equivFinOfCardEq h
  obtain ⟨E, hE⟩ :=
    ((davenport_eq_iff _ 10).1 davenport_cube_four).1 (fun k => u (e.symm k))
  have hB : IsZeroSet u (E.map e.symm.toEmbedding) := (isZeroSet_map_equiv u e.symm E).2 hE
  exact hasIncidenceIdentity_of_pairwise_disjoint u 0 (fun _ => E.map e.symm.toEmbedding)
    (fun _ => hB) (fun i j hij => absurd (Subsingleton.elim (α := Fin 1) i j) hij)

end DavenportProject.Bases

end
