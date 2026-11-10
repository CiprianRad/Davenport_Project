/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DavenportProject.Bases.CubeThree.PlaneGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! # Plane incidence counting and cap sums: Lemma 5.1(2), Section 5.2 -/
@[expose] public section
namespace DavenportProject.CubeThree.Planes
open Finset
set_option maxRecDepth 4096

/-- Number of affine planes containing the specified finite subset. -/
def containing (T : Finset Point) : ℕ := #{p : Plane | T ⊆ plane p}

/-- The incidence count in Section 5.2: count pairs consisting of a plane and a `j`-subset
of `C` inside that plane, in the two orders. -/
theorem incidence_double_count (C : Finset Point) (j : ℕ) :
    ∑ p : Plane, (#(slice C p)).choose j = ∑ T ∈ C.powersetCard j, containing T := by
  have hf (p : Plane) : (slice C p).powersetCard j =
      (C.powersetCard j).filter (fun T => T ⊆ plane p) := by
    ext T
    simp only [mem_powersetCard, mem_filter, slice, subset_inter_iff]
    tauto
  calc
    _ = ∑ p : Plane, #((slice C p).powersetCard j) := by simp only [card_powersetCard]
    _ = ∑ p : Plane, #((C.powersetCard j).filter (fun T => T ⊆ plane p)) := by simp only [hf]
    _ = _ := by
      simp only [card_eq_sum_ones, sum_filter, containing]
      rw [sum_comm]

/-- The first nonconstant incidence count: each point belongs to thirteen planes. -/
theorem incidence_one (C : Finset Point) :
    ∑ p : Plane, #(slice C p) = 13 * #C := by
  have h := incidence_double_count C 1
  simp only [Nat.choose_one_right] at h
  rw [h]
  have hf : ∀ T ∈ C.powersetCard 1, containing T = 13 := by
    intro T hT
    obtain ⟨x,rfl⟩ := card_eq_one.mp (mem_powersetCard.mp hT).2
    simpa [containing, singleton_subset_iff] using planes_through_point x
  rw [sum_congr rfl hf]
  simp [card_powersetCard, Nat.mul_comm]

/-- The second incidence count: each pair belongs to four planes. -/
theorem incidence_two (C : Finset Point) :
    ∑ p : Plane, (#(slice C p)).choose 2 = 4 * (#C).choose 2 := by
  rw [incidence_double_count]
  have hf : ∀ T ∈ C.powersetCard 2, containing T = 4 := by
    intro T hT
    obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp (mem_powersetCard.mp hT).2
    simpa [containing, insert_subset_iff, singleton_subset_iff] using planes_through_pair x y hxy
  rw [sum_congr rfl hf]
  simp [card_powersetCard, Nat.mul_comm]

/-- The third incidence count: every triple in a cap is noncollinear and determines one plane. -/
theorem incidence_three {C : Finset Point} (hC : IsCap C) :
    ∑ p : Plane, (#(slice C p)).choose 3 = (#C).choose 3 := by
  rw [incidence_double_count]
  have hf : ∀ T ∈ C.powersetCard 3, containing T = 1 := by
    intro T hT
    obtain ⟨hTC,hcard⟩ := mem_powersetCard.mp hT
    obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := card_eq_three.mp hcard
    have hs := hC x (hTC (by simp)) y (hTC (by simp)) z (hTC (by simp)) hxy hxz hyz
    simpa [containing, insert_subset_iff, singleton_subset_iff] using
      planes_through_triple x y z hxy hxz hyz hs
  rw [sum_congr rfl hf]
  simp [card_powersetCard]

/-- The histogram `nᵢ` used in the four displayed incidence equations of Section 5.2. -/
def number (C : Finset Point) (i : ℕ) : ℕ := #{p : Plane | #(slice C p) = i}

/-- Every cap-plane intersection has one of the sizes zero through four. -/
theorem slice_card_le_four {C : Finset Point} (hC : IsCap C) (p : Plane) : #(slice C p) ≤ 4 :=
  cap_plane_card_le_four (hC.mono inter_subset_left) inter_subset_right

/-- Grouping a sum over planes by their intersection sizes gives the paper's histogram. -/
theorem histogram {C : Finset Point} (hC : IsCap C) (f : ℕ → ℕ) :
    ∑ p : Plane, f #(slice C p) = ∑ i ∈ range 5, f i * number C i := by
  classical
  calc
    _ = ∑ p : Plane, ∑ i ∈ range 5, if #(slice C p) = i then f i else 0 := by
      apply sum_congr rfl
      intro p _
      simp [show #(slice C p) < 5 by have := slice_card_le_four hC p; omega]
    _ = ∑ i ∈ range 5, ∑ p : Plane, if #(slice C p) = i then f i else 0 := by rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro i _
      simp [number, ← sum_filter, Nat.mul_comm]

/-- The four incidence equations of Lemma 5.1(2), with the binomial coefficients expanded. -/
theorem incidence_equations {C : Finset Point} (hC : IsCap C) :
    number C 0 + number C 1 + number C 2 + number C 3 + number C 4 = 39 ∧
    number C 1 + 2 * number C 2 + 3 * number C 3 + 4 * number C 4 = 13 * #C ∧
    number C 2 + 3 * number C 3 + 6 * number C 4 = 4 * (#C).choose 2 ∧
    number C 3 + 4 * number C 4 = (#C).choose 3 := by
  have h0 := histogram hC (fun _ => 1)
  have h1 := histogram hC id
  have h2 := histogram hC (fun i => i.choose 2)
  have h3 := histogram hC (fun i => i.choose 3)
  simp only [sum_const, card_univ, card_planes, smul_eq_mul, mul_one] at h0
  simp only [id_eq] at h1
  rw [incidence_one] at h1
  rw [incidence_two] at h2
  rw [incidence_three hC] at h3
  norm_num [sum_range_succ, Nat.choose] at h0 h1 h2 h3
  omega

/-- Section 5.2: a cap of ten points would force `n₃+4n₀ = -4`. -/
theorem cap_not_ten {C : Finset Point} (hC : IsCap C) : #C ≠ 10 := by
  intro hcard
  obtain ⟨h0,h1,h2,h3⟩ := incidence_equations hC
  rw [hcard] at h1 h2 h3
  norm_num [Nat.choose] at h1 h2 h3
  omega

/-- Section 5.2: any larger cap contains a ten-point cap, so every cap has at most nine points. -/
theorem cap_card_le_nine {C : Finset Point} (hC : IsCap C) : #C ≤ 9 := by
  by_contra h
  obtain ⟨D,hDC,hcard⟩ := exists_subset_card_eq (show 10 ≤ #C by omega)
  exact cap_not_ten (hC.mono hDC) hcard

/-- Write a slice as a fiber, to group sums over the three parallel planes. -/
theorem slice_eq_filter (C : Finset Point) (d : Direction) (a : ZMod 3) :
    slice C (d,a) = C.filter (fun x => value d x = a) := by
  ext x
  simp

/-- The three parallel slices partition the cap. -/
theorem slice_cards_sum (C : Finset Point) (d : Direction) :
    ∑ a : ZMod 3, #(slice C (d,a)) = #C := by
  simp_rw [slice_eq_filter]
  rw [sum_card_fiberwise_eq_card_filter]
  simp

/-- Evaluate the cap sum by first grouping its points in the three parallel slices. -/
theorem value_sum_slices (C : Finset Point) (d : Direction) :
    value d (∑ x ∈ C, x) = ∑ a : ZMod 3, (#(slice C (d,a)) : ZMod 3) * a := by
  rw [value_sum]
  calc
    _ = ∑ x ∈ C, ∑ a : ZMod 3, if value d x = a then a else 0 := by simp
    _ = ∑ a : ZMod 3, ∑ x ∈ C, if value d x = a then a else 0 := by rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro a _
      rw [← sum_filter]
      simp [slice_eq_filter, nsmul_eq_mul]

/-- The three values in F₃, written explicitly for the slice arithmetic in Section 5.2. -/
theorem sum_three {M : Type*} [AddCommMonoid M] (f : ZMod 3 → M) :
    ∑ a : ZMod 3, f a = f 0 + f 1 + f 2 := by
  rw [show (univ : Finset (ZMod 3)) = {0,1,2} by decide]
  rw [sum_insert (by decide),sum_insert (by decide),sum_singleton]
  rw [add_assoc]

/-- Section 5.2: an eight-point cap has an empty affine plane, by `n₂ = 6n₀−2`. -/
theorem empty_plane_of_card_eight {C : Finset Point} (hC : IsCap C) (hcard : #C = 8) :
    ∃ p : Plane, #(slice C p) = 0 := by
  obtain ⟨h0,h1,h2,h3⟩ := incidence_equations hC
  rw [hcard] at h1 h2 h3
  norm_num [Nat.choose] at h1 h2 h3
  have hp : 0 < number C 0 := by omega
  obtain ⟨p,hp⟩ := card_pos.mp hp
  exact ⟨p,(mem_filter.mp hp).2⟩

/-- Section 5.2: the sum of an eight-point cap containing zero is nonzero. An empty plane
cannot be the zero fiber, and the other two fibers have four points each. -/
theorem sum_ne_zero_of_card_eight {C : Finset Point} (hC : IsCap C) (hcard : #C = 8)
    (hzero : (0 : Point) ∈ C) : ∑ x ∈ C, x ≠ 0 := by
  obtain ⟨⟨d,a⟩,hempty⟩ := empty_plane_of_card_eight hC hcard
  have hn0 : 0 < #(slice C (d,0)) := card_pos.mpr ⟨0,by simp [hzero]⟩
  have ha : a ≠ 0 := by rintro rfl; omega
  have hsum := slice_cards_sum C d
  rw [sum_three, hcard] at hsum
  have h0 := slice_card_le_four hC (d,0)
  have h1 := slice_card_le_four hC (d,1)
  have h2 := slice_card_le_four hC (d,2)
  have hval := value_sum_slices C d
  rw [sum_three] at hval
  have hnonzero : value d (∑ x ∈ C, x) ≠ 0 := by
    have hacases : a = 1 ∨ a = 2 := by
      fin_cases a
      · exact (ha rfl).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hacases with rfl | rfl
    · have hn2 : #(slice C (d,2)) = 4 := by omega
      rw [hempty,hn2] at hval
      norm_num at hval
      rw [hval]
      decide
    · have hn1 : #(slice C (d,1)) = 4 := by omega
      rw [hempty,hn1] at hval
      norm_num at hval
      rw [hval]
      decide
  intro hs
  exact hnonzero (by rw [hs,value_zero])

/-- Section 5.2: no affine plane misses a nine-point cap, since its other two fibers contain
at most eight points. -/
theorem slice_pos_of_card_nine {C : Finset Point} (hC : IsCap C) (hcard : #C = 9)
    (p : Plane) : 0 < #(slice C p) := by
  obtain ⟨d,a⟩ := p
  have hsum := slice_cards_sum C d
  rw [sum_three, hcard] at hsum
  have h0 := slice_card_le_four hC (d,0)
  have h1 := slice_card_le_four hC (d,1)
  have h2 := slice_card_le_four hC (d,2)
  fin_cases a
  · change 0 < #(slice C (d,0)); omega
  · change 0 < #(slice C (d,1)); omega
  · change 0 < #(slice C (d,2)); omega

/-- For a nine-point cap, the equations give `n₂ = 6n₀ = 0`. -/
theorem slice_ne_two_of_card_nine {C : Finset Point} (hC : IsCap C) (hcard : #C = 9)
    (p : Plane) : #(slice C p) ≠ 2 := by
  have hn0 : number C 0 = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have := (mem_filter.mp hp).2
    have := slice_pos_of_card_nine hC hcard p
    omega
  obtain ⟨h0,h1,h2,h3⟩ := incidence_equations hC
  rw [hcard] at h1 h2 h3
  norm_num [Nat.choose] at h1 h2 h3
  have hn2 : number C 2 = 0 := by omega
  intro hp
  have : 0 < number C 2 := card_pos.mpr ⟨p,mem_filter.mpr ⟨mem_univ _,hp⟩⟩
  omega

/-- The elementary slice arithmetic in Section 5.2: three positive sizes at most four,
none equal to two and with total nine, are `3,3,3` or a permutation of `1,4,4`. -/
theorem slice_pattern (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ha4 : a ≤ 4) (hb4 : b ≤ 4) (hc4 : c ≤ 4)
    (ha2 : a ≠ 2) (hb2 : b ≠ 2) (hc2 : c ≠ 2) (hs : a + b + c = 9) :
    (a = 3 ∧ b = 3 ∧ c = 3) ∨
      (a = 1 ∧ b = 4 ∧ c = 4) ∨ (a = 4 ∧ b = 1 ∧ c = 4) ∨
      (a = 4 ∧ b = 4 ∧ c = 1) := by omega

/-- Section 5.2: each of the thirteen functionals annihilates the sum of a nine-point cap. -/
theorem value_sum_eq_zero_of_card_nine {C : Finset Point} (hC : IsCap C) (hcard : #C = 9)
    (d : Direction) : value d (∑ x ∈ C, x) = 0 := by
  have hsum := slice_cards_sum C d
  rw [sum_three,hcard] at hsum
  have hpat := slice_pattern _ _ _
    (slice_pos_of_card_nine hC hcard (d,0)) (slice_pos_of_card_nine hC hcard (d,1))
    (slice_pos_of_card_nine hC hcard (d,2))
    (slice_card_le_four hC (d,0)) (slice_card_le_four hC (d,1)) (slice_card_le_four hC (d,2))
    (slice_ne_two_of_card_nine hC hcard (d,0)) (slice_ne_two_of_card_nine hC hcard (d,1))
    (slice_ne_two_of_card_nine hC hcard (d,2)) hsum
  rw [value_sum_slices,sum_three]
  rcases hpat with ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ <;>
    rw [h0,h1,h2] <;> decide

/-- The normal directions include the three coordinate functionals, hence separate points. -/
theorem eq_zero_of_values (x : Point) (hx : ∀ d, value d x = 0) : x = 0 := by
  funext i
  fin_cases i
  · simpa [value,normal,Fin.sum_univ_three] using hx 0
  · simpa [value,normal,Fin.sum_univ_three] using hx 9
  · simpa [value,normal,Fin.sum_univ_three] using hx 12

/-- Section 5.2: a nine-point cap has sum zero, by its three-slice patterns. -/
theorem sum_eq_zero_of_card_nine {C : Finset Point} (hC : IsCap C) (hcard : #C = 9) :
    ∑ x ∈ C, x = 0 :=
  eq_zero_of_values _ (value_sum_eq_zero_of_card_nine hC hcard)

/-- The first step of Lemma 5.1(2), Section 5.2: adjoining zero to an allowed support gives a
cap. A line through zero would give an opposite pair, and any other line a zero triple. -/
theorem cap_insert_zero {A : Finset Point} (_h0 : (0 : Point) ∉ A)
    (h2 : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → x + y ≠ 0)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → x ≠ z → y ≠ z → x + y + z ≠ 0) :
    IsCap (insert 0 A) := by
  intro x hx y hy z hz hxy hxz hyz
  rcases mem_insert.mp hx with rfl | hx <;>
    rcases mem_insert.mp hy with rfl | hy <;>
    rcases mem_insert.mp hz with rfl | hz
  · exact (hxy rfl).elim
  · exact (hxy rfl).elim
  · exact (hxz rfl).elim
  · simpa only [zero_add] using h2 y hy z hz hyz
  · exact (hyz rfl).elim
  · simpa only [add_zero] using h2 x hx z hz hxz
  · simpa only [add_zero] using h2 x hx y hy hxy
  · exact h3 x hx y hy z hz hxy hxz hyz

/-- Lemma 5.1(2), Section 5.2, for an allowed support. All three conclusions use the affine-plane
proof: the cap bound, the empty-plane argument at eight points, and the slice pattern at nine. -/
theorem support_spec {A : Finset Point} (h0 : (0 : Point) ∉ A)
    (h2 : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → x + y ≠ 0)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → x ≠ z → y ≠ z → x + y + z ≠ 0) :
    #A ≤ 8 ∧ (#A = 7 → ∑ x ∈ A, x ≠ 0) ∧ (#A = 8 → ∑ x ∈ A, x = 0) := by
  have hcap := cap_insert_zero h0 h2 h3
  have hcard : #(insert (0 : Point) A) = #A + 1 := card_insert_of_notMem h0
  have hsum : ∑ x ∈ insert (0 : Point) A, x = ∑ x ∈ A, x := by simp [h0]
  refine ⟨?_,?_,?_⟩
  · have := cap_card_le_nine hcap
    omega
  · intro hA
    have := sum_ne_zero_of_card_eight hcap (by omega) (mem_insert_self _ _)
    rwa [hsum] at this
  · intro hA
    have := sum_eq_zero_of_card_nine hcap (by omega)
    rwa [hsum] at this

end DavenportProject.CubeThree.Planes
