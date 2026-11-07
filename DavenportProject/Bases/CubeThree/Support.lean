/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Bases.CubeThree.Masks
public import DavenportProject.Bases.CubeThree.SupportCheck
public import DavenportProject.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Lemma 5.1(2)

`card_support_le_of_isShortZeroFree_cube_three`: the support of a short-zero-free sequence over
`C_3^3` has at most eight points; seven-point supports have nonzero sum and eight-point supports
sum to zero. The finite part is the kernel check of `Bases.CubeThree.SupportCheck`.
-/

public section

namespace DavenportProject

open Finset CubeThree.Support

/-!
## Soundness of the enumeration for Lemma 5.1(2)

`enumeration` turns the kernel computation `checkFrom_eq_true` into a statement about seven
or eight strictly increasing codes taken from an admissible set `B` of codes. The codes are
decoded into `(ZMod 3)^3` by `dec`, which turns `add3` into addition. `card_le_eight`,
`sum_dec_ne_zero` and `sum_dec_eq_zero` then give the three conclusions of Lemma 5.1(2) for
admissible sets of codes.
-/

namespace CubeThree.Support

theorem checkFrom_eq_true {a : ℕ} (h1 : 1 ≤ a) (h27 : a < 27) : checkFrom a = true := by
  interval_cases a
  exacts [checkFrom_1, checkFrom_2, checkFrom_3, checkFrom_4, checkFrom_5, checkFrom_6, checkFrom_7,
    checkFrom_8, checkFrom_9, checkFrom_10, checkFrom_11, checkFrom_12, checkFrom_13, checkFrom_14,
    checkFrom_15, checkFrom_16, checkFrom_17, checkFrom_18, checkFrom_19, checkFrom_20,
    checkFrom_21, checkFrom_22, checkFrom_23, checkFrom_24, checkFrom_25, checkFrom_26]

/-- Base-3 code of a point of `(ZMod 3)^3`. -/
def code (x : Fin 3 → ZMod 3) : ℕ := (x 0).val + 3 * (x 1).val + 9 * (x 2).val

/-- Decoding a natural number into `(ZMod 3)^3` (its last three base-3 digits). -/
def dec (n : ℕ) : Fin 3 → ZMod 3 := ![(n : ZMod 3), ((n / 3 : ℕ) : ZMod 3), ((n / 9 : ℕ) : ZMod 3)]

theorem cast_eq_cast {a b : ℕ} (h : a % 3 = b % 3) : (a : ZMod 3) = (b : ZMod 3) :=
  (ZMod.natCast_eq_natCast_iff' a b 3).2 h

theorem dec_add3 (a b : ℕ) : dec (add3 a b) = dec a + dec b := by
  obtain ⟨h1, h2, h3⟩ := add3_digits a b
  funext i
  fin_cases i
  · change ((add3 a b : ℕ) : ZMod 3) = (a : ZMod 3) + (b : ZMod 3)
    rw [← Nat.cast_add]; exact cast_eq_cast (by omega)
  · change ((add3 a b / 3 : ℕ) : ZMod 3) = ((a / 3 : ℕ) : ZMod 3) + ((b / 3 : ℕ) : ZMod 3)
    rw [← Nat.cast_add]; exact cast_eq_cast (by omega)
  · change ((add3 a b / 9 : ℕ) : ZMod 3) = ((a / 9 : ℕ) : ZMod 3) + ((b / 9 : ℕ) : ZMod 3)
    rw [← Nat.cast_add]; exact cast_eq_cast (by omega)

theorem dec_code (x : Fin 3 → ZMod 3) : dec (code x) = x := by
  have h0 := ZMod.val_lt (x 0)
  have h1 := ZMod.val_lt (x 1)
  have h2 := ZMod.val_lt (x 2)
  funext i
  fin_cases i
  · change ((code x : ℕ) : ZMod 3) = x 0
    conv_rhs => rw [← ZMod.natCast_zmod_val (x 0)]
    exact cast_eq_cast (by unfold code; omega)
  · change ((code x / 3 : ℕ) : ZMod 3) = x 1
    conv_rhs => rw [← ZMod.natCast_zmod_val (x 1)]
    exact cast_eq_cast (by unfold code; omega)
  · change ((code x / 9 : ℕ) : ZMod 3) = x 2
    conv_rhs => rw [← ZMod.natCast_zmod_val (x 2)]
    exact cast_eq_cast (by unfold code; omega)

theorem code_dec {n : ℕ} (hn : n < 27) : code (dec n) = n := by
  change ((n : ZMod 3)).val + 3 * ((n / 3 : ℕ) : ZMod 3).val + 9 * ((n / 9 : ℕ) : ZMod 3).val = n
  rw [ZMod.val_natCast, ZMod.val_natCast, ZMod.val_natCast]
  omega

theorem code_lt (x : Fin 3 → ZMod 3) : code x < 27 := by
  have h0 := ZMod.val_lt (x 0)
  have h1 := ZMod.val_lt (x 1)
  have h2 := ZMod.val_lt (x 2)
  unfold code
  omega

theorem code_zero : code 0 = 0 := by simp [code]

theorem dec_zero : dec 0 = 0 := by
  rw [← code_zero, dec_code]

theorem eq_zero_of_dec_eq_zero {n : ℕ} (hn : n < 27) (h : dec n = 0) : n = 0 := by
  rw [← code_dec hn, h, code_zero]

theorem code_injective : Function.Injective code :=
  Function.LeftInverse.injective dec_code

section Admissible

variable {B : Finset ℕ} (hB : ∀ n ∈ B, n < 27) (h0 : 0 ∉ B)
  (h2 : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → add3 x y ≠ 0)
  (h3 : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x ≠ y → x ≠ z → y ≠ z → add3 (add3 x y) z ≠ 0)
include hB h0 h2 h3

/-- The finite statement, read off from the kernel computation `checkFrom_eq_true`. -/
theorem enumeration {a b c d e f g : ℕ} (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B) (hd : d ∈ B)
    (he : e ∈ B) (hf : f ∈ B) (hg : g ∈ B) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e) (hef : e < f) (hfg : f < g) :
    add3 (add3 (add3 (add3 (add3 (add3 a b) c) d) e) f) g ≠ 0 ∧
      ∀ h ∈ B, g < h → add3 (add3 (add3 (add3 (add3 (add3 (add3 a b) c) d) e) f) g) h = 0 := by
  have ha0 : 1 ≤ a := Nat.pos_of_ne_zero fun e => h0 (e ▸ ha)
  have H := checkFrom_eq_true ha0 (hB a ha)
  have H := of_allFrom H hab (hB b hb)
  rw [testBit_mk_of_mem h0 h2 h3 (by simp [ha]) (by simp; omega) hb, Bool.false_or] at H
  have H := of_allFrom H hbc (hB c hc)
  rw [testBit_mk_of_mem h0 h2 h3 (by simp [ha, hb]) (by simp; omega) hc, Bool.false_or] at H
  have H := of_allFrom H hcd (hB d hd)
  rw [testBit_mk_of_mem h0 h2 h3 (by simp [ha, hb, hc]) (by simp; omega) hd, Bool.false_or] at H
  have H := of_allFrom H hde (hB e he)
  rw [testBit_mk_of_mem h0 h2 h3 (by simp [ha, hb, hc, hd]) (by simp; omega) he,
    Bool.false_or] at H
  have H := of_allFrom H hef (hB f hf)
  rw [testBit_mk_of_mem h0 h2 h3 (by simp [ha, hb, hc, hd, he]) (by simp; omega) hf,
    Bool.false_or] at H
  have H := of_allFrom H hfg (hB g hg)
  rw [testBit_mk_of_mem h0 h2 h3 (by simp [ha, hb, hc, hd, he, hf]) (by simp; omega) hg,
    Bool.false_or, Bool.and_eq_true, bne_iff_ne] at H
  refine ⟨H.1, fun h hh hgh => ?_⟩
  have H := of_allFrom H.2 hgh (hB h hh)
  rwa [testBit_mk_of_mem h0 h2 h3 (by simp [ha, hb, hc, hd, he, hf, hg]) (by simp; omega) hh,
    Bool.false_or, beq_iff_eq] at H

theorem sum_dec_ne_zero (hcard : #B = 7) : ∑ n ∈ B, dec n ≠ 0 := by
  set f := B.orderEmbOfFin hcard
  have hm := B.orderEmbOfFin_mem hcard
  have hlt : ∀ i j : Fin 7, i < j → f i < f j := fun i j h => f.strictMono h
  rw [← B.image_orderEmbOfFin_univ hcard, sum_image (f.injective.injOn), Fin.sum_univ_seven]
  simp only [← dec_add3]
  intro h
  refine (enumeration hB h0 h2 h3 (hm 0) (hm 1) (hm 2) (hm 3) (hm 4) (hm 5) (hm 6)
    (hlt 0 1 (by decide)) (hlt 1 2 (by decide)) (hlt 2 3 (by decide)) (hlt 3 4 (by decide))
    (hlt 4 5 (by decide)) (hlt 5 6 (by decide))).1 ?_
  exact eq_zero_of_dec_eq_zero (add3_lt _ _) h

theorem sum_dec_eq_zero (hcard : #B = 8) : ∑ n ∈ B, dec n = 0 := by
  set f := B.orderEmbOfFin hcard
  have hm := B.orderEmbOfFin_mem hcard
  have hlt : ∀ i j : Fin 8, i < j → f i < f j := fun i j h => f.strictMono h
  rw [← B.image_orderEmbOfFin_univ hcard, sum_image (f.injective.injOn), Fin.sum_univ_eight]
  simp only [← dec_add3]
  rw [(enumeration hB h0 h2 h3 (hm 0) (hm 1) (hm 2) (hm 3) (hm 4) (hm 5) (hm 6)
    (hlt 0 1 (by decide)) (hlt 1 2 (by decide)) (hlt 2 3 (by decide)) (hlt 3 4 (by decide))
    (hlt 4 5 (by decide)) (hlt 5 6 (by decide))).2 _ (hm 7) (hlt 6 7 (by decide)), dec_zero]

omit hB h0 h2 h3 in
theorem admissible_mono {C : Finset ℕ} (hCB : C ⊆ B) (hB : ∀ n ∈ B, n < 27) (h0 : 0 ∉ B)
    (h2 : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → add3 x y ≠ 0)
    (h3 : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x ≠ y → x ≠ z → y ≠ z → add3 (add3 x y) z ≠ 0) :
    (∀ n ∈ C, n < 27) ∧ 0 ∉ C ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → add3 x y ≠ 0) ∧
      (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x ≠ y → x ≠ z → y ≠ z → add3 (add3 x y) z ≠ 0) :=
  ⟨fun n hn => hB n (hCB hn), fun h => h0 (hCB h), fun x hx y hy => h2 x (hCB hx) y (hCB hy),
    fun x hx y hy z hz => h3 x (hCB hx) y (hCB hy) z (hCB hz)⟩

theorem card_le_eight : #B ≤ 8 := by
  by_contra hlt
  obtain ⟨C, hCB, hC⟩ := exists_subset_card_eq (show 9 ≤ #B by omega)
  obtain ⟨hC1, hC0, hC2, hC3⟩ := admissible_mono hCB hB h0 h2 h3
  have key : ∀ n ∈ C, dec n = ∑ m ∈ C, dec m := fun n hn => by
    have hsub := admissible_mono (erase_subset n C) hC1 hC0 hC2 hC3
    have hcard : #(C.erase n) = 8 := by rw [card_erase_of_mem hn, hC]
    rw [← sum_erase_add C dec hn, sum_dec_eq_zero hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hcard,
      zero_add]
  have hone : #C ≤ 1 := card_le_one.2 fun n hn m hm => by
    rw [← code_dec (hC1 n hn), ← code_dec (hC1 m hm), key n hn, key m hm]
  omega

end Admissible

theorem three_le_exponent : 3 ≤ AddMonoid.exponent (Fin 3 → ZMod 3) := by
  have hne : AddMonoid.exponent (Fin 3 → ZMod 3) ≠ 0 := AddMonoid.exponent_ne_zero_of_finite
  have h := congrFun (AddMonoid.exponent_nsmul_eq_zero (fun _ : Fin 3 => (1 : ZMod 3))) 0
  simp only [Pi.smul_apply, nsmul_eq_mul, mul_one, Pi.zero_apply,
    ZMod.natCast_eq_zero_iff] at h
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h

end CubeThree.Support

/-!
## Proof of Lemma 5.1(2)

The exponent of `(ZMod 3)^3` is `3`, so the support `A` of
a short-zero-free sequence contains no zero, no two distinct points with sum zero and no three
distinct points with sum zero (each would give a zero set of size at most three). Coding points
by `code`, the set of codes satisfies the hypotheses of the kernel-checked `enumeration`
(see `Bases/CubeThree/SupportCheck.lean`): seven admissible points never sum to
zero and eight always do. Nine admissible points cannot exist: each eight-point subset sums to
zero, so all nine points would equal the total sum.
-/

/-- **Lemma 5.1(2)** (finite computation): the support of a
short-zero-free sequence over `C_3^3` has at most eight points; every such support with seven
points has nonzero sum, and every such support with eight points has sum zero. -/
theorem card_support_le_of_isShortZeroFree_cube_three {N : ℕ} (u : Fin N → (Fin 3 → ZMod 3))
    (hu : IsShortZeroFree u) :
    #(univ.image u) ≤ 8 ∧
      (#(univ.image u) = 7 → ∑ x ∈ univ.image u, x ≠ 0) ∧
      (#(univ.image u) = 8 → ∑ x ∈ univ.image u, x = 0) := by
  set A := univ.image u
  -- zero sets of size at most three are excluded
  have hsmall : ∀ E : Finset (Fin N), E.Nonempty → #E ≤ 3 → ∑ i ∈ E, u i ≠ 0 :=
    fun E hE hc hs => absurd (hu E ⟨hE, hs⟩) (by have := three_le_exponent; omega)
  have hA : ∀ x ∈ A, ∃ i, u i = x := fun x hx => by simpa [A] using hx
  set B := A.image code
  have hB : ∀ n ∈ B, n < 27 := fun n hn => by
    obtain ⟨x, -, rfl⟩ := mem_image.1 hn
    exact code_lt x
  have h0 : 0 ∉ B := fun hn => by
    obtain ⟨x, hx, hx0⟩ := mem_image.1 hn
    obtain ⟨i, rfl⟩ := hA x hx
    refine hsmall {i} (singleton_nonempty i) (by simp) ?_
    rw [sum_singleton, ← dec_code (u i), hx0, dec_zero]
  have h2 : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → add3 x y ≠ 0 := fun x hx y hy hxy hs => by
    obtain ⟨x, hx', rfl⟩ := mem_image.1 hx
    obtain ⟨y, hy', rfl⟩ := mem_image.1 hy
    obtain ⟨i, rfl⟩ := hA x hx'
    obtain ⟨j, rfl⟩ := hA y hy'
    have hij : i ≠ j := fun e => hxy (by rw [e])
    refine hsmall {i, j} (insert_nonempty i _) (card_le_two.trans (by norm_num)) ?_
    rw [sum_pair hij, ← dec_code (u i), ← dec_code (u j), ← dec_add3, hs, dec_zero]
  have h3 : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x ≠ y → x ≠ z → y ≠ z → add3 (add3 x y) z ≠ 0 :=
    fun x hx y hy z hz hxy hxz hyz hs => by
    obtain ⟨x, hx', rfl⟩ := mem_image.1 hx
    obtain ⟨y, hy', rfl⟩ := mem_image.1 hy
    obtain ⟨z, hz', rfl⟩ := mem_image.1 hz
    obtain ⟨i, rfl⟩ := hA x hx'
    obtain ⟨j, rfl⟩ := hA y hy'
    obtain ⟨k, rfl⟩ := hA z hz'
    have hij : i ≠ j := fun e => hxy (by rw [e])
    have hik : i ≠ k := fun e => hxz (by rw [e])
    have hjk : j ≠ k := fun e => hyz (by rw [e])
    refine hsmall {i, j, k} (insert_nonempty i _) card_le_three ?_
    rw [sum_insert (by simp [hij, hik]), sum_pair hjk, ← add_assoc, ← dec_code (u i),
      ← dec_code (u j), ← dec_code (u k), ← dec_add3, ← dec_add3, hs, dec_zero]
  have hcard : #B = #A := card_image_of_injective A code_injective
  have hsum : ∑ x ∈ A, x = ∑ n ∈ B, dec n := by
    rw [sum_image (code_injective.injOn)]
    simp only [dec_code]
  refine ⟨hcard ▸ card_le_eight hB h0 h2 h3, fun h7 => ?_, fun h8 => ?_⟩
  · rw [hsum]; exact sum_dec_ne_zero hB h0 h2 h3 (hcard.trans h7)
  · rw [hsum]; exact sum_dec_eq_zero hB h0 h2 h3 (hcard.trans h8)

end DavenportProject
