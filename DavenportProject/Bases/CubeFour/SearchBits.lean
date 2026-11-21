/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportCompute.Search
public import DavenportProject.Bases.CubeFour.Codes
import Mathlib.Data.Nat.Bitwise

/-!
# The bit operations of the kernel enumeration of Lemma 5.3

Meaning of the primitives of `DavenportCompute.Search` in terms of the code arithmetic of
`DavenportCompute.Basic`:

* `force_eq`: `force n k = k n`;
* `bitB_eq`: `bitB S x` is the bit `x` of `S`;
* `negc_eq`, `addc_eq`: `negc` and `addc` are `neg4` and `add4` on codes;
* `testBit_transl2`: `transl2 S y` translates both 64-bit halves of `S`, as sets of codes, by `y`;
* `testBit_gmask`: the codes excluded by the guards.
-/

@[expose] public section

namespace DavenportProject.CubeFour

open DavenportCompute DavenportCompute.Search

theorem force_eq {α : Sort*} (n : ℕ) (k : ℕ → α) : force n k = k n := by
  cases n <;> rfl

theorem bitB_eq (S x : ℕ) : bitB S x = S.testBit x := by
  have h : Nat.land (Nat.shiftRight S x) 1 = (S >>> x) % 2 := Nat.and_one_is_mod _
  rw [bitB, h, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (S / 2 ^ x) with h0 | h0 <;> rw [h0] <;> rfl

theorem negc_eq : ∀ x < 64, negc x = neg4 x := by decide +kernel

theorem addc_eq : ∀ a < 64, ∀ b < 64, addc a b = add4 a b := by decide +kernel

/-! ## Translation of sets of codes -/

/-- The position from which `rot _ _ sh t` moves the bit at position `p`: the base-4 digit of
stride `2 ^ sh` of `p` is decreased by `t` modulo `4`. -/
def rotPre (sh t p : ℕ) : ℕ :=
  p - 2 ^ sh * (p / 2 ^ sh % 4) + 2 ^ sh * ((p / 2 ^ sh % 4 + 4 - t) % 4)

/-- The left shift of `rot`. -/
def rotA (sh t : ℕ) : ℕ := Nat.shiftLeft t sh

/-- The right shift of `rot`. -/
def rotB (sh t : ℕ) : ℕ := Nat.shiftLeft (Nat.sub 4 t) sh

/-- The block mask of `rot`: the codes whose digit is below `4 - t`. -/
def rotLow (rep sh t : ℕ) : ℕ := Nat.mul rep (Nat.sub (Nat.shiftLeft 1 (rotB sh t)) 1)

theorem rot_eq (S rep sh t : ℕ) : rot S rep sh t =
    ((S &&& rotLow rep sh t) <<< rotA sh t) |||
      ((S &&& (FULL2 ^^^ rotLow rep sh t)) >>> rotB sh t) :=
  rfl

/-- The two cases of `rot`, as a decidable statement about positions. -/
abbrev RotOK (rep sh t : ℕ) : Prop :=
  ∀ p < 128,
    (rotA sh t ≤ p ∧ (rotLow rep sh t).testBit (p - rotA sh t) = true ∧
        p - rotA sh t = rotPre sh t p ∧
        (FULL2 ^^^ rotLow rep sh t).testBit (rotB sh t + p) = false) ∨
      (¬(rotA sh t ≤ p ∧ (rotLow rep sh t).testBit (p - rotA sh t) = true) ∧
        (FULL2 ^^^ rotLow rep sh t).testBit (rotB sh t + p) = true ∧
        rotB sh t + p = rotPre sh t p)

theorem rotOK_zero : ∀ t < 4, RotOK REP0 0 t := by decide +kernel
theorem rotOK_two : ∀ t < 4, RotOK REP1 2 t := by decide +kernel
theorem rotOK_four : ∀ t < 4, RotOK REP2 4 t := by decide +kernel

theorem testBit_rot {rep sh t : ℕ} (h : RotOK rep sh t) (S : ℕ) {p : ℕ} (hp : p < 128) :
    (rot S rep sh t).testBit p = S.testBit (rotPre sh t p) := by
  rw [rot_eq, Nat.testBit_lor, Nat.testBit_shiftLeft, Nat.testBit_land, Nat.testBit_shiftRight,
    Nat.testBit_land]
  rcases h p hp with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · rw [h4, h2, decide_eq_true h1, h3]
    simp
  · rw [h2, h3]
    by_cases ha : rotA sh t ≤ p
    · have hL : (rotLow rep sh t).testBit (p - rotA sh t) = false := by simpa [ha] using h1
      rw [hL]
      simp
    · rw [decide_eq_false ha]
      simp

/-- The position `rot` moves into `p`, when the digit has been rotated in both halves. -/
def translPre (y p : ℕ) : ℕ := rotPre 0 (y % 4) (rotPre 2 (y / 4 % 4) (rotPre 4 (y / 16) p))

theorem rotPre_lt : ∀ t < 4, ∀ p < 128, rotPre 0 t p < 128 ∧ rotPre 2 t p < 128 ∧
    rotPre 4 t p < 128 := by decide +kernel

theorem testBit_transl2 (S y : ℕ) (hy : y < 64) {p : ℕ} (hp : p < 128) :
    (transl2 S y).testBit p = S.testBit (translPre y p) := by
  have h4 : y / 16 < 4 := by omega
  have e0 : Nat.land y 3 = y % 4 := Nat.and_two_pow_sub_one_eq_mod y 2
  have e1 : Nat.land (Nat.shiftRight y 2) 3 = y / 4 % 4 := by
    rw [show Nat.land (Nat.shiftRight y 2) 3 = (y >>> 2) &&& 3 from rfl,
      Nat.and_two_pow_sub_one_eq_mod _ 2, Nat.shiftRight_eq_div_pow]
  have e2 : Nat.shiftRight y 4 = y / 16 := by
    rw [show Nat.shiftRight y 4 = y >>> 4 from rfl, Nat.shiftRight_eq_div_pow]
  rw [transl2, e0, e1, e2, testBit_rot (rotOK_four _ h4) _ hp,
    testBit_rot (rotOK_two _ (Nat.mod_lt _ (by norm_num))) _ (rotPre_lt _ h4 _ hp).2.2,
    testBit_rot (rotOK_zero _ (Nat.mod_lt _ (by norm_num))) _
      (rotPre_lt _ (Nat.mod_lt _ (by norm_num)) _ (rotPre_lt _ h4 _ hp).2.2).2.1]
  rfl

/-- In each half, `translPre y` subtracts the code `y`. -/
theorem translPre_eq : ∀ y < 64, ∀ p < 128,
    translPre y p = 64 * (p / 64) + add4 (p % 64) (neg4 y) := by decide +kernel

/-- Bit `c` of the low half of `transl2 S y` is bit `c - y` of `S`. -/
theorem testBit_transl2_low (S y : ℕ) (hy : y < 64) {c : ℕ} (hc : c < 64) :
    (transl2 S y).testBit c = S.testBit (add4 c (neg4 y)) := by
  rw [testBit_transl2 S y hy (by omega), translPre_eq y hy c (by omega)]
  simp [Nat.div_eq_of_lt hc, Nat.mod_eq_of_lt hc]

/-- Bit `64 + c` of `transl2 S y` is bit `64 + (c - y)` of `S`. -/
theorem testBit_transl2_high (S y : ℕ) (hy : y < 64) {c : ℕ} (hc : c < 64) :
    (transl2 S y).testBit (64 + c) = S.testBit (64 + add4 c (neg4 y)) := by
  have h1 : (64 + c) / 64 = 1 := by omega
  have h2 : (64 + c) % 64 = c := by omega
  rw [testBit_transl2 S y hy (by omega), translPre_eq y hy (64 + c) (by omega), h1, h2]

/-! ## The guard mask -/

theorem testBit_gmask (c1 c4 c16 : ℕ) {x : ℕ} (hx : x < 64) :
    (gmask c1 c4 c16).testBit x =
      ((decide (c1 = 0) && P1 x && x != 1) || (decide (c4 = 0) && P2 x && x != 4) ||
        (decide (c16 = 0) && P3 x && x != 16)) := by
  have key : ∀ a b c : Bool, ∀ x < 64,
      (Nat.lor (cond a G1 0) (Nat.lor (cond b G4 0) (cond c G16 0))).testBit x =
        ((a && P1 x && x != 1) || (b && P2 x && x != 4) || (c && P3 x && x != 16)) := by
    decide +kernel
  have hb : ∀ n, Nat.beq n 0 = decide (n = 0) := fun n => by cases n <;> rfl
  simp only [gmask, hb]
  exact key _ _ _ x hx

end DavenportProject.CubeFour
