/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The affine-plane proof of Lemma 5.1(2), Section 5.2

The only finite checks below concern the incidence structure of affine space:
normal vectors, parallel directions, and planes through at most three points.
The cap bounds and support sums follow by the incidence double counts in the paper.
-/

@[expose] public section
namespace DavenportProject.CubeThree.Planes
open Finset

abbrev Point := Fin 3 → ZMod 3
abbrev Direction := Fin 13
abbrev Plane := Direction × ZMod 3

/-- Representatives of the thirteen nonzero normal vectors up to sign, chosen with first
nonzero coordinate one. They also represent the thirteen directions of affine lines. -/
def normal : Direction → Point :=
  ![![1,0,0], ![1,0,1], ![1,0,2], ![1,1,0], ![1,1,1], ![1,1,2],
    ![1,2,0], ![1,2,1], ![1,2,2], ![0,1,0], ![0,1,1], ![0,1,2], ![0,0,1]]

/-- The linear functional defining a parallel class of planes. -/
def value (d : Direction) (x : Point) : ZMod 3 := ∑ i, normal d i * x i

/-- An affine plane is one fiber of one of the thirteen functionals. -/
def plane (p : Plane) : Finset Point := univ.filter fun x => value p.1 x = p.2

/-- The points of a cap lying in a specified affine plane. -/
def slice (C : Finset Point) (p : Plane) : Finset Point := C ∩ plane p

/-- Over F₃, three distinct points are collinear exactly when their sum is zero. -/
def IsCap (C : Finset Point) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x ≠ y → x ≠ z → y ≠ z → x + y + z ≠ 0

/-- The four line directions contained in a plane's direction space. -/
def directions (d : Direction) : Finset Direction :=
  univ.filter fun e => value d (normal e) = 0

/-- Two distinct points have direction `e` when their difference is either representative. -/
def Parallel (e : Direction) (x y : Point) : Prop :=
  y - x = normal e ∨ x - y = normal e

instance (e : Direction) (x y : Point) : Decidable (Parallel e x y) := inferInstanceAs
  (Decidable (y - x = normal e ∨ x - y = normal e))

@[simp] theorem value_zero (d : Direction) : value d 0 = 0 := by simp [value]

theorem value_add (d : Direction) (x y : Point) : value d (x + y) = value d x + value d y := by
  simp [value, mul_add, sum_add_distrib]

theorem value_sum (d : Direction) (C : Finset Point) :
    value d (∑ x ∈ C, x) = ∑ x ∈ C, value d x := by
  simp only [value, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

@[simp] theorem mem_plane (x : Point) (p : Plane) : x ∈ plane p ↔ value p.1 x = p.2 := by
  simp [plane]

@[simp] theorem mem_slice (C : Finset Point) (p : Plane) (x : Point) :
    x ∈ slice C p ↔ x ∈ C ∧ value p.1 x = p.2 := by simp [slice]

theorem IsCap.mono {C D : Finset Point} (hC : IsCap C) (h : D ⊆ C) : IsCap D :=
  fun x hx y hy z hz => hC x (h hx) y (h hy) z (h hz)

/-- Section 5.2: each affine plane has four directions. -/
theorem card_directions (d : Direction) : #(directions d) = 4 := by
  revert d
  decide +kernel

set_option maxRecDepth 4096

/-- Every nonzero vector determines exactly one of the thirteen directions. -/
theorem unique_vector_direction : ∀ v : Point, v ≠ 0 →
    #{e : Direction | v = normal e ∨ -v = normal e} = 1 := by
  decide +kernel

/-- Section 5.2: every pair of distinct points has exactly one direction. -/
theorem unique_direction (x y : Point) (hxy : x ≠ y) :
    #{e : Direction | Parallel e x y} = 1 := by
  have h := unique_vector_direction (y-x) (sub_ne_zero.mpr hxy.symm)
  convert h using 1
  congr 1
  ext e
  simp only [mem_filter, mem_univ, true_and]
  simp [Parallel, neg_sub]

/-- A pair in an affine plane has a direction parallel to that plane. -/
theorem direction_in_plane (d e : Direction) (x y : Point)
    (h : value d x = value d y) (he : Parallel e x y) : e ∈ directions d := by
  have sub_value (v w : Point) : value d (v - w) = value d v - value d w := by
    simp [value, mul_sub, sum_sub_distrib]
  simp only [directions, mem_filter, mem_univ, true_and]
  rcases he with he | he
  · rw [← he, sub_value, h, sub_self]
  · rw [← he, sub_value, h, sub_self]

/-- Two distinct pairs sharing an endpoint and direction form a collinear triple. -/
theorem parallel_triple (e : Direction) (x y z : Point)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (hyz : y ≠ z)
    (hy : Parallel e x y) (hz : Parallel e x z) : x + y + z = 0 := by
  have hthree (x : Point) : x + x + x = 0 := by
    funext i
    change x i + x i + x i = 0
    have : (3 : ZMod 3) = 0 := by decide
    linear_combination x i * this
  rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact False.elim (hyz (sub_left_injective (hy.trans hz.symm)))
  · have h' : y + z = x + x := (sub_eq_sub_iff_add_eq_add).mp (hy.trans hz.symm)
    rw [add_assoc, h', ← add_assoc, hthree]
  · have h' : y + z = x + x := by
      have h := (sub_eq_sub_iff_add_eq_add).mp (hy.trans hz.symm)
      simpa [add_comm] using h.symm
    rw [add_assoc, h', ← add_assoc, hthree]
  · exact False.elim (hyz (sub_right_injective (hy.trans hz.symm)))

/-- Section 5.2: there are 39 affine planes. -/
@[simp] theorem card_planes : Fintype.card Plane = 39 := by decide

/-- Section 5.2: a point lies in thirteen affine planes. -/
theorem planes_through_point (x : Point) :
    #{p : Plane | x ∈ plane p} = 13 := by
  simp only [card_eq_sum_ones, sum_filter, mem_plane, Fintype.sum_prod_type]
  simp

/-- Counting planes through two points reduces to counting their common normal directions. -/
theorem planes_pair_normal (x y : Point) :
    #{p : Plane | x ∈ plane p ∧ y ∈ plane p} =
      #{d : Direction | value d x = value d y} := by
  simp only [card_eq_sum_ones, sum_filter, mem_plane, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro d _
  simp [ite_and, eq_comm]

/-- There are four normal directions perpendicular to a nonzero vector. -/
theorem perpendicular_count : ∀ v : Point, v ≠ 0 →
    #{d : Direction | value d v = 0} = 4 := by
  decide +kernel

/-- Two independent vectors determine one normal direction. In F₃, independence of two
nonzero vectors means that they are neither equal nor opposite. -/
theorem perpendicular_pair_count : ∀ v w : Point,
    v ≠ 0 → w ≠ 0 → v ≠ w → v + w ≠ 0 →
    #{d : Direction | value d v = 0 ∧ value d w = 0} = 1 := by
  decide +kernel

/-- Section 5.2: two distinct points lie in four affine planes. -/
theorem planes_through_pair (x y : Point) (hxy : x ≠ y) :
    #{p : Plane | x ∈ plane p ∧ y ∈ plane p} = 4 := by
  rw [planes_pair_normal]
  have h := perpendicular_count (x-y) (sub_ne_zero.mpr hxy)
  convert h using 1
  congr 1
  ext d
  simp only [mem_filter, mem_univ, true_and]
  simp [value, mul_sub, sum_sub_distrib, sub_eq_zero]

/-- Counting planes through three points reduces to common normal directions. -/
theorem planes_triple_normal (x y z : Point) :
    #{p : Plane | x ∈ plane p ∧ y ∈ plane p ∧ z ∈ plane p} =
      #{d : Direction | value d x = value d y ∧ value d x = value d z} := by
  simp only [card_eq_sum_ones, sum_filter, mem_plane, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro d _
  simp [ite_and, eq_comm]

/-- The sum of the two differences from `x` is the sum of the three points, in characteristic
three. This identifies the noncollinearity condition used in the paper. -/
theorem sum_differences (x y z : Point) : (y-x)+(z-x) = x + y + z := by
  funext i
  change (y i-x i)+(z i-x i) = x i+y i+z i
  have h : (3 : ZMod 3) = 0 := by decide
  linear_combination -(x i) * h

/-- Section 5.2: a noncollinear triple determines exactly one affine plane. -/
theorem planes_through_triple (x y z : Point)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hs : x + y + z ≠ 0) :
    #{p : Plane | x ∈ plane p ∧ y ∈ plane p ∧ z ∈ plane p} = 1 := by
  rw [planes_triple_normal]
  have h := perpendicular_pair_count (y-x) (z-x) (sub_ne_zero.mpr hxy.symm)
    (sub_ne_zero.mpr hxz.symm) (fun h => hyz (sub_left_injective h))
    (by rwa [sum_differences])
  convert h using 1
  congr 1
  ext d
  simp only [mem_filter, mem_univ, true_and]
  simp only [value, Pi.sub_apply, mul_sub, sum_sub_distrib, sub_eq_zero]
  simp only [eq_comm]

/-- A two-element set containing `x` has a uniquely determined other endpoint. -/
theorem pair_eq_of_mem {T : Finset Point} (hT : #T = 2) {x : Point} (hx : x ∈ T) :
    ∃ y, x ≠ y ∧ T = {x,y} := by
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hT
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b,hab,rfl⟩
  · exact ⟨a,hab.symm,by rw [pair_comm]⟩

/-- Both endpoints of a pair have direction `e`. -/
def PairInDirection (e : Direction) (T : Finset Point) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Parallel e x y

instance (e : Direction) (T : Finset Point) : Decidable (PairInDirection e T) :=
  inferInstanceAs (Decidable (∀ x ∈ T, ∀ y ∈ T, x ≠ y → Parallel e x y))

theorem pair_in_direction {e : Direction} {x y : Point} (hxy : x ≠ y) :
    PairInDirection e {x,y} ↔ Parallel e x y := by
  constructor
  · intro h
    exact h x (mem_insert_self _ _) y (mem_insert_of_mem (mem_singleton_self _)) hxy
  · intro h a ha b hb hab
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact h
    · exact h.elim Or.inr Or.inl
    · exact (hab rfl).elim

/-- The pairs of cap points in one direction, as in the plane bound's pair count. -/
def pairs (C : Finset Point) (e : Direction) : Finset (Finset Point) :=
  (C.powersetCard 2).filter (PairInDirection e)

/-- In a cap, two different pairs of the same direction cannot share an endpoint. -/
theorem pairs_disjoint {C : Finset Point} (hC : IsCap C) (e : Direction) :
    ((pairs C e : Finset (Finset Point)) : Set (Finset Point)).PairwiseDisjoint id := by
  intro T hT U hU hTU
  change T ∈ pairs C e at hT
  change U ∈ pairs C e at hU
  simp only [pairs, mem_filter, mem_powersetCard] at hT hU
  apply disjoint_left.mpr
  intro x hxT hxU
  obtain ⟨y,hxy,rfl⟩ := pair_eq_of_mem hT.1.2 hxT
  obtain ⟨z,hxz,rfl⟩ := pair_eq_of_mem hU.1.2 hxU
  have hyz : y ≠ z := by rintro rfl; exact hTU rfl
  exact hC x (hT.1.1 (by simp)) y (hT.1.1 (by simp)) z (hU.1.1 (by simp))
    hxy hxz hyz (parallel_triple e x y z hxy hxz hyz
      ((pair_in_direction hxy).mp hT.2) ((pair_in_direction hxz).mp hU.2))

/-- Disjoint pairs in one direction use two different points each. -/
theorem twice_pairs_le {C : Finset Point} (hC : IsCap C) (e : Direction) :
    2 * #(pairs C e) ≤ #C := by
  have h := card_biUnion (pairs_disjoint hC e)
  have hsub : (pairs C e).biUnion id ⊆ C := by
    intro x hx
    obtain ⟨T,hT,hx⟩ := mem_biUnion.mp hx
    exact (mem_powersetCard.mp (mem_filter.mp hT).1).1 hx
  have hcards : ∑ T ∈ pairs C e, #T = 2 * #(pairs C e) := by
    calc
      _ = ∑ _T ∈ pairs C e, 2 := by
        apply sum_congr rfl
        intro T hT
        exact (mem_powersetCard.mp (mem_filter.mp hT).1).2
      _ = _ := by simp [Nat.mul_comm]
  simp only [id_eq] at h
  rw [hcards] at h
  exact h ▸ card_le_card hsub

/-- Double-counting pairs in an affine plane by their four directions. -/
theorem pairs_count {C : Finset Point} {p : Plane} (hC : C ⊆ plane p) :
    ∑ e ∈ directions p.1, #(pairs C e) = (#C).choose 2 := by
  classical
  simp only [pairs, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  have hinner : ∀ T ∈ C.powersetCard 2,
      (∑ e ∈ directions p.1, if PairInDirection e T then 1 else 0) = 1 := by
    intro T hT
    obtain ⟨hTC,hcard⟩ := mem_powersetCard.mp hT
    obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hcard
    simp_rw [pair_in_direction hxy]
    have hx := (mem_plane x p).mp (hC (hTC (by simp : x ∈ ({x,y} : Finset Point))))
    have hy := (mem_plane y p).mp (hC (hTC (by simp : y ∈ ({x,y} : Finset Point))))
    have hdir : ∀ e, Parallel e x y → e ∈ directions p.1 :=
      fun e he => direction_in_plane p.1 e x y (hx.trans hy.symm) he
    have heq : (directions p.1).filter (fun e => Parallel e x y) =
        univ.filter (fun e => Parallel e x y) := by
      ext e
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨And.right, fun h => ⟨hdir e h,h⟩⟩
    rw [← sum_filter, ← card_eq_sum_ones, heq]
    exact unique_direction x y hxy
  rw [sum_congr rfl hinner]
  simp [card_powersetCard]

/-- Lemma 5.1(2), Section 5.2: an affine plane contains at most four cap points.
Five points would have ten pairs; each of the four directions accounts for at most two. -/
theorem cap_plane_card_le_four {C : Finset Point} (hC : IsCap C) {p : Plane}
    (hp : C ⊆ plane p) : #C ≤ 4 := by
  by_contra h
  obtain ⟨D,hDC,hDcard⟩ := exists_subset_card_eq (show 5 ≤ #C by omega)
  have hD := hC.mono hDC
  have hpair := pairs_count (hDC.trans hp)
  rw [hDcard] at hpair
  have hle : ∑ e ∈ directions p.1, #(pairs D e) ≤ 8 := by
    calc
      _ ≤ ∑ _e ∈ directions p.1, 2 := by
        apply sum_le_sum
        intro e _
        have := twice_pairs_le hD e
        omega
      _ = 8 := by rw [sum_const, card_directions]; decide
  norm_num [Nat.choose] at hpair
  omega

end DavenportProject.CubeThree.Planes
