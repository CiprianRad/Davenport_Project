/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George C. Rad
-/
module

public import DavenportProject.Bases.CubeThree.IdentityCheck
public import DavenportProject.Bases.CubeThree.Masks
public import DavenportProject.Defs
public import Mathlib.Data.ZMod.Basic
import DavenportProject.Bases.CubeThree.Normalize
import DavenportProject.Bases.CubeThree.Support
import DavenportProject.Identities.Operations
import DavenportProject.Invariants
import DavenportProject.Transfer.Olson
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Sort

/-!
# Lemma 5.1(1)

`hasIncidenceIdentity_cube_three_ten`: every ten-term sequence over `C_3^3` has an integral
`𝓘_1`-identity. A short zero set gives two disjoint zero sets (`D(C_3^3) = 7`); otherwise a linear
normalization and sorting reduce to the kernel-checked enumeration of
`Bases.CubeThree.IdentityCheck`.
-/

/-!
## Soundness of the enumeration for Lemma 5.1(1)

`enumeration` turns the kernel computation `tail4_eq_true` into a statement about a
non-decreasing sequence of ten codes `c` without zero sets of size at most three, containing
`1 = e₁` and `3 = e₂` twice each and either containing `9 = e₃` or lying in the plane of
codes below `9`: such a sequence has an integral `𝓘_1`-identity.

Each level of the enumeration is discharged by `step`: an admissible next code is never
skipped. The leaf is discharged by `leaf_sound`, the soundness of the certificate test.
-/

public section

namespace DavenportProject.CubeThree.Identity

open Finset DavenportProject
open DavenportProject.CubeThree.Support

theorem add3_add3_self (a : ℕ) : add3 (add3 a a) a = 0 := by
  obtain ⟨h1, h2, h3⟩ := add3_digits a a
  rw [add3]
  generalize add3 a a = r at h1 h2 h3
  omega

theorem neg3_add3_self (a : ℕ) (h : a < 27) : neg3 (add3 a a) = a := by
  obtain ⟨h1, h2, h3⟩ := add3_digits a a
  rw [neg3, add3]
  generalize add3 a a = r at h1 h2 h3
  omega

/-- A variant of `testBit_mk_eq_false` for lists with repetitions. -/
theorem testBit_mk_eq_false' {h : ℕ} (h0 : h ≠ 0) :
    ∀ {l : List ℕ}, (∀ q ∈ l, h ≠ neg3 q) →
      (∀ q ∈ l, ∀ r ∈ l, h ≠ neg3 (add3 q r)) → (mk l).testBit h = false
  | [], _, _ => by
    rw [CubeThree.Support.mk, show (1 : ℕ) = 1 <<< 0 from rfl,
      testBit_one_shiftLeft]
    simpa using Ne.symm h0
  | p :: l, h1, h2 => by
    rw [CubeThree.Support.mk, Nat.testBit_lor,
      testBit_mk_eq_false' h0 (fun q hq => h1 q (by simp [hq]))
        (fun q hq r hr => h2 q (by simp [hq]) r (by simp [hr])),
      testBit_bad_eq_false (h1 p (by simp)) (fun q hq => h2 q (by simp [hq]) p (by simp))]
    rfl

section Admissible

variable {B : Finset ℕ} (hB : ∀ n ∈ B, n < 27) (h0 : 0 ∉ B)
  (h2 : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → add3 x y ≠ 0)
  (h3 : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x ≠ y → x ≠ z → y ≠ z → add3 (add3 x y) z ≠ 0)
include hB h0 h2 h3

/-- One level of the enumeration: an admissible next code `b` is not skipped. -/
theorem step {p p2 b : ℕ} {l : List ℕ} {rest : Bool} (H : (skip (p :: p2 :: l) b || rest) = true)
    (hl : ∀ q ∈ p :: p2 :: l, q ∈ B ∧ q ≤ p) (hb : b ∈ B) (hpb : p ≤ b)
    (h9 : ¬ (p < 9 ∧ 9 < b)) (hm : b = p → p2 ≠ b) : rest = true := by
  suffices hs : skip (p :: p2 :: l) b = false by rwa [hs, Bool.false_or] at H
  have h9' : (decide (p < 9) && decide (9 < b)) = false := by
    simpa only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_and_or] using h9
  rw [skip, h9', Bool.false_or]
  by_cases hbp : b = p
  · have := hm hbp
    subst hbp
    simpa using this
  · have hlt : p < b := lt_of_le_of_ne hpb (Ne.symm hbp)
    have hne : ∀ q ∈ p :: p2 :: l, q ≠ b := fun q hq => by have := (hl q hq).2; omega
    simp only [show (b == p) = false by simpa using hbp, Bool.false_eq_true, ↓reduceIte]
    refine testBit_mk_eq_false' (fun e => h0 (e ▸ hb)) (fun q hq e => ?_) (fun q hq r hr e => ?_)
    · exact h2 q (hl q hq).1 b hb (hne q hq) (e ▸ add3_neg3 q)
    · by_cases hqr : q = r
      · subst hqr
        exact hne q hq (by rw [e, neg3_add3_self q (hB q (hl q hq).1)])
      · exact h3 q (hl q hq).1 r (hl r hr).1 b hb hqr (hne q hq) (hne r hr) (e ▸ add3_neg3 _)

end Admissible

theorem leaf_sound {l : List ℕ} (h : leaf l = true) {n : ℕ} (f : Fin n → ℕ)
    (hf : l.reverse = List.ofFn f) : HasIncidenceIdentity ℤ (fun i => dec (f i)) 1 := by
  unfold leaf at h
  split at h
  · rw [hf] at h
    exact hasIncidenceIdentity_of_checkCert f h
  · exact absurd h (by simp)

/-- The finite statement, read off from the kernel computation `tail4_eq_true`. -/
theorem enumeration (c : Fin 10 → ℕ) (hc : ∀ i, c i < 27) (hmono : Monotone c)
    (hshort : ∀ E : Finset (Fin 10), IsZeroSet (fun i => dec (c i)) E → 3 < #E)
    (h1 : ∃ i j, i ≠ j ∧ c i = 1 ∧ c j = 1) (h3 : ∃ i j, i ≠ j ∧ c i = 3 ∧ c j = 3)
    (h9 : (∃ i, c i = 9) ∨ ∀ i, c i < 9) :
    HasIncidenceIdentity ℤ (fun i => dec (c i)) 1 := by
  -- no zero sets of size one, two or three
  have hz : ∀ i, c i ≠ 0 := by
    intro i e
    have := hshort {i} ⟨⟨i, mem_singleton_self i⟩, by simp [e, dec_zero]⟩
    simp at this
  have hpair : ∀ i j, i ≠ j → add3 (c i) (c j) ≠ 0 := by
    intro i j hij e
    have := hshort {i, j} ⟨⟨i, by simp⟩, by rw [sum_pair hij, ← dec_add3, e, dec_zero]⟩
    rw [card_pair hij] at this
    omega
  have htrip : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → add3 (add3 (c i) (c j)) (c k) ≠ 0 := by
    intro i j k hij hik hjk e
    have := hshort {i, j, k} ⟨⟨i, by simp⟩, by
      rw [sum_insert (by simp [hij, hik]), sum_pair hjk, ← add_assoc, ← dec_add3, ← dec_add3, e,
        dec_zero]⟩
    rw [card_eq_three.2 ⟨i, j, k, hij, hik, hjk, rfl⟩] at this
    omega
  have no3 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → c i = c j → c j ≠ c k := by
    intro i j k hij hik hjk e1 e2
    apply htrip i j k hij hik hjk
    rw [e1, e2]
    exact add3_add3_self _
  -- the admissible set of codes
  set B := univ.image c with hBdef
  have memB : ∀ i, c i ∈ B := fun i => mem_image_of_mem c (mem_univ i)
  have hB : ∀ n ∈ B, n < 27 := by
    intro n hn
    obtain ⟨i, -, rfl⟩ := mem_image.1 hn
    exact hc i
  have hB0 : 0 ∉ B := by
    intro hn
    obtain ⟨i, -, e⟩ := mem_image.1 hn
    exact hz i e
  have hB2 : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → add3 x y ≠ 0 := by
    intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx
    obtain ⟨j, -, rfl⟩ := mem_image.1 hy
    exact hpair i j fun e => hxy (e ▸ rfl)
  have hB3 : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x ≠ y → x ≠ z → y ≠ z → add3 (add3 x y) z ≠ 0 := by
    intro x hx y hy z hz hxy hxz hyz
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx
    obtain ⟨j, -, rfl⟩ := mem_image.1 hy
    obtain ⟨k, -, rfl⟩ := mem_image.1 hz
    exact htrip i j k (fun e => hxy (e ▸ rfl)) (fun e => hxz (e ▸ rfl)) (fun e => hyz (e ▸ rfl))
  -- monotonicity
  have m : ∀ i j : Fin 10, i.val ≤ j.val → c i ≤ c j := fun i j h => hmono (Fin.le_def.2 h)
  have m01 := m 0 1 (by decide)
  have m12 := m 1 2 (by decide)
  have m23 := m 2 3 (by decide)
  have m34 := m 3 4 (by decide)
  have m45 := m 4 5 (by decide)
  have m56 := m 5 6 (by decide)
  have m67 := m 6 7 (by decide)
  have m78 := m 7 8 (by decide)
  have m89 := m 8 9 (by decide)
  -- the prefix `1, 1, 3, 3`
  have c0 : c 0 = 1 := by
    obtain ⟨i, j, hij, hi, hj⟩ := h1
    have := m 0 i (Nat.zero_le _)
    have := hz 0
    omega
  have c1 : c 1 = 1 := by
    obtain ⟨i, j, hij, hi, hj⟩ := h1
    have hij' := Fin.val_ne_of_ne hij
    rcases (show 1 ≤ i.val ∨ 1 ≤ j.val by omega) with h | h
    · have := m 1 i h
      omega
    · have := m 1 j h
      omega
  have c2ne1 : c 2 ≠ 1 := fun e =>
    no3 0 1 2 (by decide) (by decide) (by decide) (by rw [c0, c1]) (by rw [c1, e])
  have c2ne2 : c 2 ≠ 2 := fun e => hpair 0 2 (by decide) (by rw [c0, e]; decide)
  have c3le : c 3 ≤ 3 := by
    obtain ⟨i, j, hij, hi, hj⟩ := h3
    have hij' := Fin.val_ne_of_ne hij
    have hi2 : 2 ≤ i.val := by
      by_contra h
      have := m i 1 (by omega)
      omega
    have hj2 : 2 ≤ j.val := by
      by_contra h
      have := m j 1 (by omega)
      omega
    rcases (show 3 ≤ i.val ∨ 3 ≤ j.val by omega) with h | h
    · have := m 3 i h
      omega
    · have := m 3 j h
      omega
  have c2 : c 2 = 3 := by omega
  have c3 : c 3 = 3 := by omega
  have hB1 : 1 ∈ B := c0 ▸ memB 0
  have hB3' : 3 ∈ B := c2 ▸ memB 2
  -- the guard on `9 = e₃`
  have g9 : ∀ i j : Fin 10, i.val + 1 = j.val → ¬ (c i < 9 ∧ 9 < c j) := by
    rintro i j hij ⟨hi, hj⟩
    rcases h9 with ⟨k, hk⟩ | hall
    · by_cases hki : k.val ≤ i.val
      · have := m k i hki
        omega
      · have := m j k (by omega)
        omega
    · have := hall j
      omega
  -- the six levels
  have H := tail4_eq_true (a := c 4) (by omega) (hc 4)
  rw [tail4] at H
  have H := step hB hB0 hB2 hB3 H (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      refine ⟨?_, by omega⟩
      rcases hq with rfl | rfl | rfl | rfl <;> first | exact hB3' | exact hB1) (memB 4) (by omega)
    (by have := g9 3 4 rfl; rwa [c3] at this)
    (fun e => absurd (c3.trans e.symm)
      (no3 2 3 4 (by decide) (by decide) (by decide) (c2.trans c3.symm)))
  have H := of_allFrom H m45 (hc 5)
  rw [tail5] at H
  have H := step hB hB0 hB2 hB3 H (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      refine ⟨?_, by omega⟩
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact memB _ | exact hB3' | exact hB1) (memB 5) m45 (g9 4 5 rfl)
    (fun e e' => no3 3 4 5 (by decide) (by decide) (by decide) (c3.trans (e'.trans e)) e.symm)
  have H := of_allFrom H m56 (hc 6)
  have H := step hB hB0 hB2 hB3 H (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      refine ⟨?_, by omega⟩
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact memB _ | exact hB3' | exact hB1) (memB 6) m56 (g9 5 6 rfl)
    (fun e e' => no3 4 5 6 (by decide) (by decide) (by decide) (e'.trans e) e.symm)
  have H := of_allFrom H m67 (hc 7)
  have H := step hB hB0 hB2 hB3 H (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      refine ⟨?_, by omega⟩
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact memB _ | exact hB3' | exact hB1) (memB 7) m67 (g9 6 7 rfl)
    (fun e e' => no3 5 6 7 (by decide) (by decide) (by decide) (e'.trans e) e.symm)
  have H := of_allFrom H m78 (hc 8)
  have H := step hB hB0 hB2 hB3 H (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      refine ⟨?_, by omega⟩
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact memB _ | exact hB3' | exact hB1) (memB 8) m78 (g9 7 8 rfl)
    (fun e e' => no3 6 7 8 (by decide) (by decide) (by decide) (e'.trans e) e.symm)
  have H := of_allFrom H m89 (hc 9)
  have H := step hB hB0 hB2 hB3 H (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      refine ⟨?_, by omega⟩
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact memB _ | exact hB3' | exact hB1) (memB 9) m89 (g9 8 9 rfl)
    (fun e e' => no3 7 8 9 (by decide) (by decide) (by decide) (e'.trans e) e.symm)
  exact leaf_sound H c (by simp [List.ofFn_succ, c0, c1, c2, c3])

end DavenportProject.CubeThree.Identity

end

/-!
## Reduction to the enumeration for Lemma 5.1(1)

Let `u` be a ten-term sequence over `(ZMod 3)^3` without zero sets of size at most three, in
which two distinct values `x ≠ y` occur twice each.

* `hasIncidenceIdentity_of_doubled`: a linear map sends `x, y` to `e₁, e₂`
  (`exists_det_ne_zero`, `exists_addHom_of_det`); if some term then has a nonzero third
  coordinate, a second linear map fixing `e₁, e₂` sends it to `e₃`.
* `hasIncidenceIdentity_of_normalized`: after sorting the positions by the codes `enc` of the
  terms (`Tuple.sort`), the code sequence satisfies the hypotheses of `enumeration`.
-/

public section

namespace DavenportProject.CubeThree.Identity

open Finset DavenportProject

/-- The base-3 code of a point of `(ZMod 3)^3`. -/
def enc (x : Fin 3 → ZMod 3) : ℕ := (x 0).val + 3 * (x 1).val + 9 * (x 2).val

theorem enc_lt (x : Fin 3 → ZMod 3) : enc x < 27 := by
  have := (x 0).val_lt; have := (x 1).val_lt; have := (x 2).val_lt
  unfold enc; omega

theorem dec_enc (x : Fin 3 → ZMod 3) : dec (enc x) = x := by
  have h0 := (x 0).val_lt; have h1 := (x 1).val_lt; have h2 := (x 2).val_lt
  have h3 : (3 : ZMod 3) = 0 := by decide
  have h9 : (9 : ZMod 3) = 0 := by decide
  ext i
  fin_cases i
  · change ((enc x / 3 ^ 0 : ℕ) : ZMod 3) = x 0
    rw [pow_zero, Nat.div_one, enc, show (9 : ℕ) = 3 * 3 by rfl]
    push_cast
    simp [h3, h9]
  · change ((enc x / 3 ^ 1 : ℕ) : ZMod 3) = x 1
    rw [show enc x / 3 ^ 1 = (x 1).val + 3 * (x 2).val by unfold enc; omega]
    push_cast
    simp [h3]
  · change ((enc x / 3 ^ 2 : ℕ) : ZMod 3) = x 2
    rw [show enc x / 3 ^ 2 = (x 2).val by unfold enc; omega, ZMod.natCast_zmod_val]

theorem enc_lt_nine {x : Fin 3 → ZMod 3} (h : x 2 = 0) : enc x < 9 := by
  have := (x 0).val_lt; have := (x 1).val_lt
  unfold enc; rw [h, ZMod.val_zero]; omega

/-- A sequence without short zero sets, with `e₁` and `e₂` twice each and either `e₃` or only
terms in the plane `x₂ = 0`, has an integral `𝓘_1`-identity. -/
theorem hasIncidenceIdentity_of_normalized (v : Fin 10 → (Fin 3 → ZMod 3))
    (hshort : ∀ E, IsZeroSet v E → 3 < #E)
    (h1 : ∃ i j, i ≠ j ∧ v i = Pi.single 0 1 ∧ v j = Pi.single 0 1)
    (h2 : ∃ i j, i ≠ j ∧ v i = Pi.single 1 1 ∧ v j = Pi.single 1 1)
    (h3 : (∃ k, v k = Pi.single 2 1) ∨ ∀ k, v k 2 = 0) :
    HasIncidenceIdentity ℤ v 1 := by
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin 10), Monotone fun i => enc (v (σ i)) :=
    ⟨_, Tuple.monotone_sort fun i => enc (v i)⟩
  have hdc : (fun i => dec (enc (v (σ i)))) = fun i => v (σ i) := funext fun i => dec_enc _
  have hv : v = fun i => (fun j => v (σ j)) (σ.symm i) := funext fun i => by simp
  rw [hv]
  refine DavenportProject.hasIncidenceIdentity_comp_equiv (R := ℤ) (fun j => v (σ j))
    σ.symm ?_
  rw [← hdc]
  have hcode : ∀ {i : Fin 10} {x : Fin 3 → ZMod 3}, v i = x →
      enc (v (σ (σ.symm i))) = enc x := by
    intro i x h
    simp [h]
  refine enumeration (fun i => enc (v (σ i))) (fun i => enc_lt _) hmono (fun E hE => ?_) ?_ ?_ ?_
  · rw [hdc, ← DavenportProject.isZeroSet_map_equiv] at hE
    simpa using hshort _ hE
  · obtain ⟨i, j, hij, hi, hj⟩ := h1
    exact ⟨σ.symm i, σ.symm j, σ.symm.injective.ne hij, hcode hi, hcode hj⟩
  · obtain ⟨i, j, hij, hi, hj⟩ := h2
    exact ⟨σ.symm i, σ.symm j, σ.symm.injective.ne hij, hcode hi, hcode hj⟩
  · rcases h3 with ⟨k, hk⟩ | hall
    · exact Or.inl ⟨σ.symm k, hcode hk⟩
    · exact Or.inr fun i => enc_lt_nine (hall (σ i))

/-- The case of two distinct values occurring twice each. -/
theorem hasIncidenceIdentity_of_doubled (u : Fin 10 → (Fin 3 → ZMod 3))
    (hshort : ∀ E, IsZeroSet u E → 3 < #E) {x y : Fin 3 → ZMod 3} (hxy : x ≠ y)
    (hx : ∃ i j, i ≠ j ∧ u i = x ∧ u j = x) (hy : ∃ i j, i ≠ j ∧ u i = y ∧ u j = y) :
    HasIncidenceIdentity ℤ u 1 := by
  obtain ⟨i, i', hii', hi, hi'⟩ := hx
  obtain ⟨j, j', hjj', hj, hj'⟩ := hy
  have hij : i ≠ j := fun e => hxy (hi ▸ hj ▸ congrArg u e)
  have hne : ∀ k, u k ≠ 0 := fun k e => by
    have := hshort {k} ⟨⟨k, mem_singleton_self k⟩, by simp [e]⟩
    simp at this
  have hneg : -x ≠ y := fun e => by
    have := hshort {i, j} ⟨⟨i, by simp⟩, by rw [sum_pair hij, hi, hj, ← e, add_neg_cancel]⟩
    rw [card_pair hij] at this
    omega
  obtain ⟨k, hk⟩ := exists_det_ne_zero (hi ▸ hne i) (hj ▸ hne j) hxy hneg
  obtain ⟨φ, hφ, hφM⟩ := exists_addHom_of_det _ hk
  refine hasIncidenceIdentity_of_comp φ hφ ?_
  set u₁ := fun i => φ (u i)
  have hshort₁ : ∀ E, IsZeroSet u₁ E → 3 < #E := fun E hE =>
    hshort E ((isZeroSet_comp_iff φ hφ u E).1 hE)
  have hx₁ : ∀ {k}, u k = x → u₁ k = Pi.single 0 1 := fun h => by
    simp only [u₁, h]; exact hφM 0
  have hy₁ : ∀ {k}, u k = y → u₁ k = Pi.single 1 1 := fun h => by
    simp only [u₁, h]; exact hφM 1
  have h1 : ∃ i j, i ≠ j ∧ u₁ i = Pi.single 0 1 ∧ u₁ j = Pi.single 0 1 :=
    ⟨i, i', hii', hx₁ hi, hx₁ hi'⟩
  have h2 : ∃ i j, i ≠ j ∧ u₁ i = Pi.single 1 1 ∧ u₁ j = Pi.single 1 1 :=
    ⟨j, j', hjj', hy₁ hj, hy₁ hj'⟩
  by_cases hw : ∃ k, u₁ k 2 ≠ 0
  · obtain ⟨k, hk⟩ := hw
    obtain ⟨ψ, hψ, hψM⟩ := exists_addHom_of_det ![Pi.single 0 1, Pi.single 1 1, u₁ k]
      (by rw [det_e₁_e₂]; exact hk)
    refine hasIncidenceIdentity_of_comp ψ hψ ?_
    have he₁ : ψ (Pi.single 0 1) = Pi.single 0 1 := hψM 0
    have he₂ : ψ (Pi.single 1 1) = Pi.single 1 1 := hψM 1
    refine hasIncidenceIdentity_of_normalized _ (fun E hE => hshort₁ E
      ((isZeroSet_comp_iff ψ hψ u₁ E).1 hE)) ?_ ?_ (Or.inl ⟨k, hψM 2⟩)
    · obtain ⟨a, b, hab, ha, hb⟩ := h1
      exact ⟨a, b, hab, by rw [ha, he₁], by rw [hb, he₁]⟩
    · obtain ⟨a, b, hab, ha, hb⟩ := h2
      exact ⟨a, b, hab, by rw [ha, he₂], by rw [hb, he₂]⟩
  · simp only [not_exists, not_not] at hw
    exact hasIncidenceIdentity_of_normalized u₁ hshort₁ h1 h2 (Or.inr hw)

end DavenportProject.CubeThree.Identity

end

/-!
## Proof of Lemma 5.1(1)

Proof (with a smaller normalization than the paper's):
* A zero set `E` with `#E ≤ 3` leaves at least seven terms outside it, which contain a zero
  set since `D(C_3^3) = 7` (Olson, `davenport_pi_zmod_prime_pow`); two disjoint zero sets give
  an identity (`hasIncidenceIdentity_of_pairwise_disjoint`, `t = 1`).
* Otherwise the sequence is short-zero-free. Its support has at most eight points
  (`card_support_le_of_isShortZeroFree_cube_three`) and every multiplicity is at most two, so
  two distinct values `x, y` occur twice each. A linear normalization sends `x, y` to
  `e₁, e₂` and, if possible, a third term to `e₃` (`hasIncidenceIdentity_of_doubled`). After
  sorting by codes, the 3,382 resulting cases are checked by the kernel against explicit
  certificates (`IdentityCheck`, `IdentityData`, and `enumeration` above): 2,209 disjoint pairs
  of zero sets, 1,137
  identities with five zero sets and 36 with seven, all with coefficients `±1`.
-/

public section

namespace DavenportProject.CubeThree.Identity

open Finset DavenportProject

/-- `D(C_3^3) = 7`: every seven-term sequence over `(ZMod 3)^3` has a zero set. -/
theorem exists_isZeroSet_seven (v : Fin 7 → (Fin 3 → ZMod 3)) : ∃ E, IsZeroSet v E := by
  have h := davenport_pi_zmod_prime_pow 3 (r := 3) fun _ => 1
  have h7 : davenport (Fin 3 → ZMod 3) = 7 := h.trans (by decide)
  exact ((davenport_eq_iff _ 7).1 h7).1 v

/-- A zero set of size at most three gives an integral `𝓘_1`-identity. -/
theorem hasIncidenceIdentity_of_card_le_three (u : Fin 10 → (Fin 3 → ZMod 3))
    {E : Finset (Fin 10)} (hE : IsZeroSet u E) (hcard : #E ≤ 3) :
    HasIncidenceIdentity ℤ u 1 := by
  obtain ⟨S, hS, hS7⟩ := exists_subset_card_eq (s := Eᶜ) (n := 7)
    (by rw [card_compl, Fintype.card_fin]; omega)
  set e := S.orderEmbOfFin hS7
  obtain ⟨F', hF'⟩ := exists_isZeroSet_seven fun i => u (e i)
  set F := F'.map e.toEmbedding
  have hF : IsZeroSet u F := by
    refine ⟨hF'.1.map, ?_⟩
    rw [sum_map]
    exact hF'.2
  have hdisj : Disjoint E F := by
    rw [disjoint_iff_ne]
    rintro a ha b hb rfl
    obtain ⟨i, -, rfl⟩ := mem_map.1 hb
    have := hS (S.orderEmbOfFin_mem hS7 i)
    exact (mem_compl.1 this) ha
  refine hasIncidenceIdentity_of_pairwise_disjoint u 1 ![E, F] ?_ ?_
  · intro k
    fin_cases k
    exacts [hE, hF]
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hdisj
    · exact hdisj.symm
    · exact absurd rfl hij

theorem nsmul_three (x : Fin 3 → ZMod 3) : 3 • x = 0 := by
  ext i
  simp only [Pi.smul_apply, Pi.zero_apply]
  generalize x i = a
  revert a
  decide

/-- Without zero sets of size at most three, two distinct values occur twice each. -/
theorem exists_doubled (u : Fin 10 → (Fin 3 → ZMod 3)) (hshort : ∀ E, IsZeroSet u E → 3 < #E) :
    ∃ x y, x ≠ y ∧ (∃ i j, i ≠ j ∧ u i = x ∧ u j = x) ∧ (∃ i j, i ≠ j ∧ u i = y ∧ u j = y) := by
  classical
  have hexp : AddMonoid.exponent (Fin 3 → ZMod 3) ≤ 3 :=
    Nat.le_of_dvd (by norm_num) (AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero nsmul_three)
  have hS := (card_support_le_of_isShortZeroFree_cube_three u
    fun E hE => lt_of_le_of_lt hexp (hshort E hE)).1
  set S := univ.image u
  set fib := fun x => #{i | u i = x}
  have hfib : ∀ x, fib x ≤ 2 := by
    intro x
    by_contra h
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := two_lt_card_iff.1 (not_le.1 h)
    simp only [mem_filter, mem_univ, true_and] at ha hb hc
    have := hshort {a, b, c} ⟨⟨a, by simp⟩, by
      rw [sum_insert (by simp [hab, hac]), sum_pair hbc, ha, hb, hc, ← nsmul_three x]
      abel⟩
    rw [card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩] at this
    omega
  have hsum : 10 = ∑ x ∈ S, fib x := by
    simpa using card_eq_sum_card_image u univ
  have hle : ∑ x ∈ S, fib x ≤ ∑ x ∈ S, (1 + if 2 ≤ fib x then 1 else 0) :=
    sum_le_sum fun x hx => by
      have := hfib x
      split_ifs with h
      · omega
      · omega
  rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one, ← card_filter] at hle
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.1 (show 1 < #{x ∈ S | 2 ≤ fib x} by omega)
  have hpair : ∀ z ∈ {x ∈ S | 2 ≤ fib x}, ∃ i j, i ≠ j ∧ u i = z ∧ u j = z := by
    intro z hz
    obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.1 (mem_filter.1 hz).2
    simp only [mem_filter, mem_univ, true_and] at hi hj
    exact ⟨i, j, hij, hi, hj⟩
  exact ⟨x, y, hxy, hpair x hx, hpair y hy⟩

end DavenportProject.CubeThree.Identity

end

public section

namespace DavenportProject

open Finset DavenportProject
open DavenportProject.CubeThree.Identity

open Finset

/-- **Lemma 5.1(1)** (finite computation): every ten-term sequence over
`C_3^3` has an integral `𝓘_1`-identity. -/
theorem hasIncidenceIdentity_cube_three_ten (u : Fin 10 → (Fin 3 → ZMod 3)) :
    HasIncidenceIdentity ℤ u 1 := by
  by_cases hs : ∃ E, IsZeroSet u E ∧ #E ≤ 3
  · obtain ⟨E, hE, hcard⟩ := hs
    exact hasIncidenceIdentity_of_card_le_three u hE hcard
  · have hshort : ∀ E, IsZeroSet u E → 3 < #E := fun E hE =>
      not_le.1 fun h => hs ⟨E, hE, h⟩
    obtain ⟨x, y, hxy, hx, hy⟩ := exists_doubled u hshort
    exact hasIncidenceIdentity_of_doubled u hshort hxy hx hy

end DavenportProject

end
