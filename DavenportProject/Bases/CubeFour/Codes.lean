/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportCompute.Basic
public import DavenportCompute.Oracle
public import DavenportProject.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Codes over `C_4^3` and the certificate checker

Soundness of the computation library `DavenportCompute` used for Lemma 5.3:
* the normal form predicates (`P1g`, `P2g`, `P3g`, `IsNormal`) and list-level short-zero-freeness;
* the bit sets and sum sets of the enumeration (`mem_shiftSet`, `mem_R1_iff`, …);
* decoding of codes (`dec`, `enc`, `dec_add4`, `dec_codeSum`);
* soundness of the certificate checker (`hasIncidenceIdentity_of_check`, `longZero_sound`).
-/

@[expose] public section

namespace DavenportProject.CubeFour

open Finset DavenportCompute

/-!
## Shared definitions for the proof of Lemma 5.3

Group level (`G = (ZMod 4)^3`, standard basis `e₀ e₁ e₂`):
* `P1g x`: `2x ≠ 0`, i.e. some coordinate of `x` is odd;
* `P2g x`: `2x ∉ {0, 2e₀}`, i.e. `x₁` or `x₂` is odd;
* `P3g x`: `2x ∉ {0, 2e₀, 2e₁, 2e₀ + 2e₁}`, i.e. `x₂` is odd;
* `mult v x`: the multiplicity of `x` in the sequence `v`;
* `IsNormal v`: the normalization of a sequence used by the enumeration. For `k = 0, 1, 2`, the
  basis vector `e_k` occurs in `v` unless no term satisfies `P(k+1)g`, and no term satisfying
  `P(k+1)g` occurs more often than `e_k`.

Code level (lists of codes `< 64`, see `DavenportCompute.Basic`):
* `ListSZF F`: no nonempty sublist of `F` of length at most four has code sum zero;
* `Guards F`: `1 ∈ F` unless no entry satisfies `P1`, `4 ∈ F` unless no entry satisfies `P2`,
  `16 ∈ F` unless no entry satisfies `P3`.
-/

/-- `2x ≠ 0`: some coordinate of `x` is odd. -/
def P1g (x : Fin 3 → ZMod 4) : Prop := 2 • x ≠ 0

/-- `2x ∉ {0, 2e₀}`: the coordinate `x₁` or `x₂` is odd. -/
def P2g (x : Fin 3 → ZMod 4) : Prop := 2 • x ≠ 0 ∧ 2 • x ≠ 2 • Pi.single 0 1

/-- `2x ∉ {0, 2e₀, 2e₁, 2e₀ + 2e₁}`: the coordinate `x₂` is odd. -/
def P3g (x : Fin 3 → ZMod 4) : Prop :=
  2 • x ≠ 0 ∧ 2 • x ≠ 2 • Pi.single 0 1 ∧ 2 • x ≠ 2 • Pi.single 1 1 ∧
    2 • x ≠ 2 • (Pi.single 0 1 + Pi.single 1 1)

/-- The multiplicity of `x` in the sequence `v`. -/
noncomputable def mult {ι : Type*} [Fintype ι] (v : ι → (Fin 3 → ZMod 4)) (x : Fin 3 → ZMod 4) :
    ℕ := by
  classical exact #{i | v i = x}

/-- The normalization used by the enumeration (see the section docstring). -/
def IsNormal {ι : Type*} [Fintype ι] (v : ι → (Fin 3 → ZMod 4)) : Prop :=
  ((∃ i, v i = Pi.single 0 1) ∨ ∀ i, ¬ P1g (v i)) ∧
    (∀ x, P1g x → mult v x ≤ mult v (Pi.single 0 1)) ∧
  ((∃ i, v i = Pi.single 1 1) ∨ ∀ i, ¬ P2g (v i)) ∧
    (∀ x, P2g x → mult v x ≤ mult v (Pi.single 1 1)) ∧
  ((∃ i, v i = Pi.single 2 1) ∨ ∀ i, ¬ P3g (v i)) ∧
    (∀ x, P3g x → mult v x ≤ mult v (Pi.single 2 1))

/-- No nonempty sublist of length at most four has code sum zero. -/
def ListSZF (F : List ℕ) : Prop :=
  ∀ q : List ℕ, q.Sublist F → q ≠ [] → q.length ≤ 4 → codeSum q ≠ 0

/-- The normalization guards at the level of codes. -/
def Guards (F : List ℕ) : Prop :=
  (1 ∈ F ∨ ∀ y ∈ F, P1 y = false) ∧ (4 ∈ F ∨ ∀ y ∈ F, P2 y = false) ∧
    (16 ∈ F ∨ ∀ y ∈ F, P3 y = false)

/-!
## Semantics of the bit sets and sum sets of the Lemma 5.3 computation

Facts about the code-level definitions of `DavenportCompute`, needed for the soundness
of the enumeration (`DavenportProject.Bases.CubeFour.Enumeration`):

* code arithmetic: `add4` is commutative and associative, `add4 a (neg4 a) = 0`, `0` is neutral
  on codes `< 64`, and `codeSum` is invariant under permutations (`codeSum_perm`);
* bit sets: `mem_or`, `mem_bit`, and `mem_shiftSet` (the translate `S + x`);
* sum sets: every member of `R1 p`, `R2 p`, `R3 p` is the code sum of a sublist of `p` of length
  `1`, `2`, `3` (`mem_R1_iff`, `exists_sublist_of_mem_R2`, `exists_sublist_of_mem_R3`);
* the loop `allFrom` (`allFrom_eq_true_iff`).
-/

/-! ### Code arithmetic -/

theorem add4_eq (a b : ℕ) : add4 a b =
    (a % 4 + b % 4) % 4 + 4 * ((a / 4 % 4 + b / 4 % 4) % 4) +
      16 * ((a / 16 % 4 + b / 16 % 4) % 4) := rfl

theorem neg4_eq (a : ℕ) : neg4 a =
    (4 - a % 4) % 4 + 4 * ((4 - a / 4 % 4) % 4) + 16 * ((4 - a / 16 % 4) % 4) := rfl

theorem digits_lt (u v w : ℕ) : u % 4 + 4 * (v % 4) + 16 * (w % 4) < 64 := by omega

theorem digits_mod_four (u v w : ℕ) : (u % 4 + 4 * (v % 4) + 16 * (w % 4)) % 4 = u % 4 := by
  omega

theorem digits_div_four_mod_four (u v w : ℕ) :
    (u % 4 + 4 * (v % 4) + 16 * (w % 4)) / 4 % 4 = v % 4 := by
  omega

theorem digits_div_sixteen_mod_four (u v w : ℕ) :
    (u % 4 + 4 * (v % 4) + 16 * (w % 4)) / 16 % 4 = w % 4 := by
  omega

theorem add4_lt (a b : ℕ) : add4 a b < 64 := digits_lt ..

theorem neg4_lt (a : ℕ) : neg4 a < 64 := digits_lt ..

theorem add4_comm (a b : ℕ) : add4 a b = add4 b a := by
  rw [add4_eq, add4_eq, Nat.add_comm (a % 4), Nat.add_comm (a / 4 % 4),
    Nat.add_comm (a / 16 % 4)]

theorem add4_mod_four (a b : ℕ) : add4 a b % 4 = (a % 4 + b % 4) % 4 := by
  rw [add4_eq, digits_mod_four]

theorem add4_div_four_mod_four (a b : ℕ) :
    add4 a b / 4 % 4 = (a / 4 % 4 + b / 4 % 4) % 4 := by
  rw [add4_eq, digits_div_four_mod_four]

theorem add4_div_sixteen_mod_four (a b : ℕ) :
    add4 a b / 16 % 4 = (a / 16 % 4 + b / 16 % 4) % 4 := by
  rw [add4_eq, digits_div_sixteen_mod_four]

theorem add4_assoc (a b c : ℕ) : add4 (add4 a b) c = add4 a (add4 b c) := by
  have h (u v w : ℕ) :
      ((u % 4 + v % 4) % 4 + w % 4) % 4 = (u % 4 + (v % 4 + w % 4) % 4) % 4 := by
    omega
  rw [add4_eq (add4 a b), add4_eq a (add4 b c), add4_mod_four, add4_mod_four,
    add4_div_four_mod_four, add4_div_four_mod_four, add4_div_sixteen_mod_four,
    add4_div_sixteen_mod_four, h a, h (a / 4), h (a / 16)]

theorem add4_left_comm (a b c : ℕ) : add4 a (add4 b c) = add4 b (add4 a c) := by
  rw [← add4_assoc, add4_comm a b, add4_assoc]

theorem add4_neg4 (a : ℕ) : add4 a (neg4 a) = 0 := by
  have h (u : ℕ) : (u % 4 + (4 - u % 4) % 4) % 4 = 0 := by omega
  rw [add4_eq, neg4_eq, digits_mod_four, digits_div_four_mod_four,
    digits_div_sixteen_mod_four, h, h, h]

theorem add4_zero {a : ℕ} (ha : a < 64) : add4 a 0 = a := by
  rw [add4_eq]
  omega

theorem codeSum_singleton {a : ℕ} (ha : a < 64) : codeSum [a] = a := add4_zero ha

/-- The code sum of a list does not depend on the order of its entries. -/
theorem codeSum_perm {q q' : List ℕ} (h : q.Perm q') : codeSum q = codeSum q' := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [codeSum, ih]
  | swap x y l => exact add4_left_comm y x (codeSum l)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Bit sets -/

theorem toNat_toUInt64_mod (x : ℕ) : x.toUInt64.toNat % 64 = x % 64 := by
  simp [Nat.toUInt64_eq]

theorem bne_eq_toNat_bne (a b : UInt64) : (a != b) = (a.toNat != b.toNat) := by
  rw [Bool.eq_iff_iff]
  simp [UInt64.toNat_inj]

/-- Membership in a bit set is a bit test; the code is taken modulo `64`. -/
theorem mem_eq_testBit (S : UInt64) (x : ℕ) : mem S x = S.toNat.testBit (x % 64) := by
  unfold mem
  rw [Nat.testBit, bne_eq_toNat_bne, UInt64.toNat_and, UInt64.toNat_shiftRight,
    toNat_toUInt64_mod, Nat.and_comm]
  rfl

theorem toNat_bit (x : ℕ) : (bit x).toNat = 2 ^ (x % 64) := by
  unfold bit
  rw [UInt64.toNat_shiftLeft, toNat_toUInt64_mod, UInt64.toNat_one, Nat.one_shiftLeft,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (Nat.mod_lt x (by decide)))]

theorem mem_zero (x : ℕ) : mem 0 x = false := by
  rw [mem_eq_testBit, UInt64.toNat_zero, Nat.zero_testBit]

/-- Membership in a union of bit sets. -/
theorem mem_or (S T : UInt64) (x : ℕ) : mem (S ||| T) x = (mem S x || mem T x) := by
  rw [mem_eq_testBit, mem_eq_testBit, mem_eq_testBit, UInt64.toNat_or, Nat.testBit_or]

/-- Membership in a singleton bit set. -/
theorem mem_bit {x y : ℕ} (hx : x < 64) (hy : y < 64) : mem (bit x) y = decide (x = y) := by
  rw [mem_eq_testBit, toNat_bit, Nat.testBit_two_pow, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem mem_shiftAux {S T : UInt64} {x t : ℕ} (ht : t < 64) (n : ℕ) :
    mem (shiftAux S x n T) t = true ↔
      mem T t = true ∨ ∃ b < n, mem S b = true ∧ add4 b x = t := by
  induction n generalizing T with
  | zero => simp [shiftAux]
  | succ n ih =>
    rw [shiftAux, ih]
    by_cases hn : mem S n = true
    · rw [ite_eq_left hn, mem_or, mem_bit (add4_lt n x) ht, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro ((h | h) | ⟨b, hb, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨n, by omega, hn, h⟩
        · exact Or.inr ⟨b, by omega, h⟩
      · rintro (h | ⟨b, hb, hS, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
          · exact Or.inr ⟨b, hb, hS, h⟩
          · exact Or.inl (Or.inr h)
    · rw [ite_eq_right hn]
      constructor
      · rintro (h | ⟨b, hb, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨b, by omega, h⟩
      · rintro (h | ⟨b, hb, hS, h⟩)
        · exact Or.inl h
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
          · exact Or.inr ⟨b, hb, hS, h⟩
          · exact absurd hS hn

/-- `shiftSet S x` is the translate `S + x`. (The bound `hx` is not needed.) -/
theorem mem_shiftSet {S : UInt64} {x t : ℕ} (hx : x < 64) (ht : t < 64) :
    mem (shiftSet S x) t = true ↔ ∃ b < 64, mem S b = true ∧ add4 b x = t := by
  have _ := hx
  rw [shiftSet, mem_shiftAux ht, mem_zero]
  simp

/-! ### Sum sets -/

/-- `R1 p` is the set of entries of `p`. -/
theorem mem_R1_iff {p : List ℕ} (hp : ∀ y ∈ p, y < 64) {s : ℕ} (hs : s < 64) :
    mem (R1 p) s = true ↔ s ∈ p := by
  induction p with
  | nil => simp [R1, mem_zero]
  | cons x p ih =>
    rw [R1, mem_or, mem_bit (hp x (by simp)) hs, Bool.or_eq_true,
      ih (fun y hy => hp y (by simp [hy]))]
    simp [eq_comm, or_comm]

theorem exists_sublist_of_mem_R1 {p : List ℕ} (hp : ∀ y ∈ p, y < 64) {s : ℕ} (hs : s < 64)
    (h : mem (R1 p) s = true) : ∃ q, q.Sublist p ∧ q.length = 1 ∧ codeSum q = s :=
  ⟨[s], List.singleton_sublist.2 ((mem_R1_iff hp hs).1 h), rfl, codeSum_singleton hs⟩

/-- Every member of `R2 p` is the code sum of a sublist of `p` of length two. -/
theorem exists_sublist_of_mem_R2 {p : List ℕ} (hp : ∀ y ∈ p, y < 64) {s : ℕ} (hs : s < 64)
    (h : mem (R2 p) s = true) : ∃ q, q.Sublist p ∧ q.length = 2 ∧ codeSum q = s := by
  induction p with
  | nil => simp [R2, mem_zero] at h
  | cons x p ih =>
    have hx : x < 64 := hp x (by simp)
    have hp' : ∀ y ∈ p, y < 64 := fun y hy => hp y (by simp [hy])
    rw [R2, mem_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨q, hq, hl, hsum⟩ := ih hp' h
      exact ⟨q, hq.cons x, hl, hsum⟩
    · obtain ⟨b, hb, hmem, rfl⟩ := (mem_shiftSet hx hs).1 h
      refine ⟨[x, b], (List.singleton_sublist.2 ((mem_R1_iff hp' hb).1 hmem)).cons_cons x,
        rfl, ?_⟩
      rw [codeSum, codeSum_singleton hb, add4_comm]

/-- Every member of `R3 p` is the code sum of a sublist of `p` of length three. -/
theorem exists_sublist_of_mem_R3 {p : List ℕ} (hp : ∀ y ∈ p, y < 64) {s : ℕ} (hs : s < 64)
    (h : mem (R3 p) s = true) : ∃ q, q.Sublist p ∧ q.length = 3 ∧ codeSum q = s := by
  induction p with
  | nil => simp [R3, mem_zero] at h
  | cons x p ih =>
    have hx : x < 64 := hp x (by simp)
    have hp' : ∀ y ∈ p, y < 64 := fun y hy => hp y (by simp [hy])
    rw [R3, mem_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨q, hq, hl, hsum⟩ := ih hp' h
      exact ⟨q, hq.cons x, hl, hsum⟩
    · obtain ⟨b, hb, hmem, rfl⟩ := (mem_shiftSet hx hs).1 h
      obtain ⟨q, hq, hl, hsum⟩ := exists_sublist_of_mem_R2 hp' hb hmem
      refine ⟨x :: q, hq.cons_cons x, by simp [hl], ?_⟩
      rw [codeSum, hsum, add4_comm]

/-! ### Loops -/

/-- `allFrom f x n` tests `f` on the interval `[x, x + n)`. -/
theorem allFrom_eq_true_iff {f : ℕ → Bool} {x n : ℕ} :
    allFrom f x n = true ↔ ∀ y, x ≤ y → y < x + n → f y = true := by
  induction n generalizing x with
  | zero =>
    simp only [allFrom, true_iff]
    intro y h₁ h₂
    omega
  | succ n ih =>
    rw [allFrom, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h₀, h⟩ y hxy hy
      rcases Nat.eq_or_lt_of_le hxy with rfl | hxy
      · exact h₀
      · exact h y hxy (by omega)
    · intro h
      exact ⟨h x (Nat.le_refl x) (by omega), fun y hy₁ hy₂ => h y (by omega) (by omega)⟩

/-!
## Codes of elements of `C_m^3`

The element `(x₀, x₁, x₂)` of `(ZMod m)^3` has the code `x₀ + m x₁ + m² x₂` (see
`DavenportCompute.Basic`). `dec m a` decodes the code `a` and `enc m x` encodes `x`.

For `m = 4`, the code operations of `DavenportCompute` are sound: `add4` and `codeSum` decode to
addition and summation (`dec_add4`, `dec_codeSum`), the tests `P1`, `P2`, `P3` decode to `P1g`,
`P2g`, `P3g` (`P1_enc`, `P2_enc`, `P3_enc`), and `ListSZF (List.ofFn c)` holds when the decoded
sequence has no zero set of size at most four (`listSZF_ofFn`).
-/

/-- Decode the code `a = x₀ + m x₁ + m² x₂` into an element of `C_m^3 = Fin 3 → ZMod m`. -/
def dec (m a : ℕ) : Fin 3 → ZMod m := fun i => (DavenportCompute.digit m a i : ZMod m)

/-- Encode an element of `C_m^3` as `x₀ + m x₁ + m² x₂`. -/
def enc (m : ℕ) (x : Fin 3 → ZMod m) : ℕ := (x 0).val + m * (x 1).val + m * m * (x 2).val

/-! ### Decoding and encoding -/

/-- The digits of `enc m x` are the coordinates of `x`. -/
theorem digit_enc {m : ℕ} [NeZero m] (x : Fin 3 → ZMod m) (i : Fin 3) :
    digit m (enc m x) i = (x i).val := by
  have hm : 0 < m := Nat.pos_of_neZero m
  have ha := ZMod.val_lt (x 0)
  have hb := ZMod.val_lt (x 1)
  have hc := ZMod.val_lt (x 2)
  set a := (x 0).val
  set b := (x 1).val
  set c := (x 2).val
  have e1 : enc m x = a + m * (b + m * c) := by simp only [enc, a, b, c]; ring
  fin_cases i
  · simp only [digit, Fin.zero_eta, Fin.isValue, pow_zero, Nat.div_one, e1]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · simp only [digit, Fin.mk_one, Fin.isValue, pow_one, e1]
    rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt ha, zero_add, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hb]
  · have e2 : enc m x = (a + m * b) + (m * m) * c := by rw [e1]; ring
    have hab : a + m * b < m * m := by nlinarith
    simp only [digit, Fin.reduceFinMk, Fin.isValue, e2, pow_two]
    rw [Nat.add_mul_div_left _ _ (Nat.mul_pos hm hm), Nat.div_eq_of_lt hab, zero_add,
      Nat.mod_eq_of_lt hc]

/-- Decoding inverts encoding. -/
theorem dec_enc {m : ℕ} [NeZero m] (x : Fin 3 → ZMod m) : dec m (enc m x) = x := by
  funext i
  simp [dec, digit_enc]

/-- Codes are less than `m ^ 3`. -/
theorem enc_lt {m : ℕ} [NeZero m] (x : Fin 3 → ZMod m) : enc m x < m ^ 3 := by
  have ha := ZMod.val_lt (x 0)
  have hb := ZMod.val_lt (x 1)
  have hc := ZMod.val_lt (x 2)
  simp only [enc]
  nlinarith

/-- Encoding inverts decoding on codes `< 64`. -/
theorem enc_dec {a : ℕ} (h : a < 64) : enc 4 (dec 4 a) = a := by
  simp only [enc, dec, digit, ZMod.val_natCast]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  omega

/-- The code `0` decodes to `0`. -/
theorem dec_zero (m : ℕ) : dec m 0 = 0 := by
  funext i
  simp [dec, digit]

theorem natCast_eq_natCast_of_mod_four {a b : ℕ} (h : a % 4 = b % 4) :
    (a : ZMod 4) = (b : ZMod 4) :=
  (ZMod.natCast_eq_natCast_iff' a b 4).2 h

/-- The base-4 digits of `add4 a b`. -/
theorem add4_digits (a b : ℕ) : add4 a b % 4 = (a % 4 + b % 4) % 4 ∧
    add4 a b / 4 % 4 = (a / 4 % 4 + b / 4 % 4) % 4 ∧
    add4 a b / 16 % 4 = (a / 16 % 4 + b / 16 % 4) % 4 := by
  unfold add4
  have h1 : (a % 4 + b % 4) % 4 < 4 := Nat.mod_lt _ (by decide)
  have h2 : (a / 4 % 4 + b / 4 % 4) % 4 < 4 := Nat.mod_lt _ (by decide)
  have h3 : (a / 16 % 4 + b / 16 % 4) % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize (a % 4 + b % 4) % 4 = x at *
  generalize (a / 4 % 4 + b / 4 % 4) % 4 = y at *
  generalize (a / 16 % 4 + b / 16 % 4) % 4 = z at *
  omega

/-- `add4` decodes to addition. -/
theorem dec_add4 (a b : ℕ) : dec 4 (add4 a b) = dec 4 a + dec 4 b := by
  obtain ⟨h0, h1, h2⟩ := add4_digits a b
  funext i
  simp only [dec, Pi.add_apply, ← Nat.cast_add]
  apply natCast_eq_natCast_of_mod_four
  fin_cases i <;> simp [digit, h0, h1, h2]

/-- `codeSum` decodes to the sum. -/
theorem dec_codeSum (q : List ℕ) : dec 4 (codeSum q) = (q.map (dec 4)).sum := by
  induction q with
  | nil => simp [codeSum, dec_zero]
  | cons x p ih => simp [codeSum, dec_add4, ih]

/-! ### The tests `P1`, `P2`, `P3` -/

theorem two_nsmul_eq_two_nsmul_iff (x y : Fin 3 → ZMod 4) :
    2 • x = 2 • y ↔ 2 * x 0 = 2 * y 0 ∧ 2 * x 1 = 2 * y 1 ∧ 2 * x 2 = 2 * y 2 := by
  simp [funext_iff, Fin.forall_fin_succ, nsmul_eq_mul]

theorem P1g_iff (x : Fin 3 → ZMod 4) :
    P1g x ↔ ¬ (2 * x 0 = 0 ∧ 2 * x 1 = 0 ∧ 2 * x 2 = 0) := by
  rw [P1g, Ne, ← smul_zero (2 : ℕ), two_nsmul_eq_two_nsmul_iff]
  simp

theorem P2g_iff (x : Fin 3 → ZMod 4) :
    P2g x ↔ ¬ (2 * x 0 = 0 ∧ 2 * x 1 = 0 ∧ 2 * x 2 = 0) ∧
      ¬ (2 * x 0 = 2 ∧ 2 * x 1 = 0 ∧ 2 * x 2 = 0) := by
  rw [P2g, Ne, Ne, ← smul_zero (2 : ℕ), two_nsmul_eq_two_nsmul_iff,
    two_nsmul_eq_two_nsmul_iff]
  simp

theorem P3g_iff (x : Fin 3 → ZMod 4) :
    P3g x ↔ ¬ (2 * x 0 = 0 ∧ 2 * x 1 = 0 ∧ 2 * x 2 = 0) ∧
      ¬ (2 * x 0 = 2 ∧ 2 * x 1 = 0 ∧ 2 * x 2 = 0) ∧
      ¬ (2 * x 0 = 0 ∧ 2 * x 1 = 2 ∧ 2 * x 2 = 0) ∧
      ¬ (2 * x 0 = 2 ∧ 2 * x 1 = 2 ∧ 2 * x 2 = 0) := by
  rw [P3g, Ne, Ne, Ne, Ne, ← smul_zero (2 : ℕ), two_nsmul_eq_two_nsmul_iff,
    two_nsmul_eq_two_nsmul_iff, two_nsmul_eq_two_nsmul_iff, two_nsmul_eq_two_nsmul_iff]
  simp

/-- `P1` decodes to `P1g`. -/
theorem P1_enc (x : Fin 3 → ZMod 4) : P1 (enc 4 x) = true ↔ P1g x := by
  rw [P1g_iff, enc]
  exact (by decide : ∀ a b c : ZMod 4, P1 (a.val + 4 * b.val + 4 * 4 * c.val) = true ↔
    ¬ (2 * a = 0 ∧ 2 * b = 0 ∧ 2 * c = 0)) (x 0) (x 1) (x 2)

/-- `P2` decodes to `P2g`. -/
theorem P2_enc (x : Fin 3 → ZMod 4) : P2 (enc 4 x) = true ↔ P2g x := by
  rw [P2g_iff, enc]
  exact (by decide : ∀ a b c : ZMod 4, P2 (a.val + 4 * b.val + 4 * 4 * c.val) = true ↔
    ¬ (2 * a = 0 ∧ 2 * b = 0 ∧ 2 * c = 0) ∧ ¬ (2 * a = 2 ∧ 2 * b = 0 ∧ 2 * c = 0))
    (x 0) (x 1) (x 2)

/-- `P3` decodes to `P3g`. -/
theorem P3_enc (x : Fin 3 → ZMod 4) : P3 (enc 4 x) = true ↔ P3g x := by
  rw [P3g_iff, enc]
  exact (by decide : ∀ a b c : ZMod 4, P3 (a.val + 4 * b.val + 4 * 4 * c.val) = true ↔
    ¬ (2 * a = 0 ∧ 2 * b = 0 ∧ 2 * c = 0) ∧ ¬ (2 * a = 2 ∧ 2 * b = 0 ∧ 2 * c = 0) ∧
      ¬ (2 * a = 0 ∧ 2 * b = 2 ∧ 2 * c = 0) ∧ ¬ (2 * a = 2 ∧ 2 * b = 2 ∧ 2 * c = 0))
    (x 0) (x 1) (x 2)

/-- The code of `e₀`. -/
theorem enc_e0 : enc 4 (Pi.single 0 1) = 1 := by decide

/-- The code of `e₁`. -/
theorem enc_e1 : enc 4 (Pi.single 1 1) = 4 := by decide

/-- The code of `e₂`. -/
theorem enc_e2 : enc 4 (Pi.single 2 1) = 16 := by decide

/-! ### Short zero sets -/

/-- If the decoded sequence has no zero set of size at most four, then no nonempty sublist of
length at most four of the code list has code sum zero. -/
theorem listSZF_ofFn {N : ℕ} (c : Fin N → ℕ) (hc : ∀ i, c i < 64)
    (h : ∀ E : Finset (Fin N), IsZeroSet (fun k => dec 4 (c k)) E → 4 < #E) :
    ListSZF (List.ofFn c) := by
  -- The bound `hc` is not needed, since `dec_codeSum` holds for all codes.
  have _ := hc
  intro q hq hne hlen hsum
  obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hq
  let e : Fin q.length ↪ Fin N := g.toEmbedding.trans (finCongr List.length_ofFn).toEmbedding
  have he : ∀ i, q.get i = c (e i) := by
    intro i
    rw [hg i]
    simp only [List.get_ofFn]
    rfl
  have hz : IsZeroSet (fun k => dec 4 (c k)) (univ.map e) := by
    refine ⟨?_, ?_⟩
    · exact ⟨e ⟨0, List.length_pos_iff.mpr hne⟩, mem_map_of_mem _ (mem_univ _)⟩
    · have hs := dec_codeSum q
      rw [hsum, dec_zero] at hs
      rw [Finset.sum_map, hs]
      simp_rw [← he]
      simp
  have := h _ hz
  simp only [card_map, card_univ, Fintype.card_fin] at this
  omega

/-!
## Soundness of the certificate checker

`toSet N E` is the set of positions
`j < N` whose bit is set in the mask `E`.

* `hasIncidenceIdentity_of_check`: if `DavenportCompute.check m t (List.ofFn f) cert = true`,
  then the decoded sequence `k ↦ dec m (f k)` has an integral `𝓘_t`-identity;
* `longZero_sound`: if `DavenportCompute.longZero (List.ofFn f) Z = true`, then `toSet N Z` is a
  zero set of the decoded sequence with at least fifteen elements.
-/

/-- The index set encoded by a mask. -/
def toSet (N E : ℕ) : Finset (Fin N) := Finset.univ.filter fun j => E.testBit j

theorem mem_toSet {N E : ℕ} {j : Fin N} : j ∈ toSet N E ↔ E.testBit j = true := by
  simp [toSet]

theorem maskSum_ofFn (g : ℕ → ℕ) {N : ℕ} (f : Fin N → ℕ) (E j₀ : ℕ) :
    maskSum g (List.ofFn f) E j₀ = ∑ k : Fin N, if E.testBit (j₀ + k) then g (f k) else 0 := by
  induction N generalizing j₀ with
  | zero => simp [maskSum]
  | succ n ih =>
    have hk : ∀ k : Fin n, j₀ + 1 + (k : ℕ) = j₀ + ((k : ℕ) + 1) := fun k => by omega
    rw [List.ofFn_succ, maskSum, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, add_zero, Fin.val_succ, hk]

/-- `maskSum` is a sum over the positions of the mask. -/
theorem maskSum_ofFn_eq_sum (g : ℕ → ℕ) {N : ℕ} (f : Fin N → ℕ) (E : ℕ) :
    maskSum g (List.ofFn f) E 0 = ∑ k ∈ toSet N E, g (f k) := by
  rw [maskSum_ofFn, toSet, Finset.sum_filter]
  simp

theorem natCast_eq_zero_of_mod {m s : ℕ} (h : s % m = 0) : (s : ZMod m) = 0 := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  simp

/-- A mask accepted by `isZeroMask` encodes a zero set of the decoded sequence. -/
theorem isZeroSet_of_isZeroMask {m N : ℕ} (f : Fin N → ℕ) {E : ℕ}
    (h : isZeroMask m (List.ofFn f) E = true) :
    IsZeroSet (fun k => dec m (f k)) (toSet N E) := by
  simp only [isZeroMask, Bool.and_eq_true, List.any_eq_true, List.mem_range, List.length_ofFn,
    beq_iff_eq, maskSum_ofFn_eq_sum] at h
  obtain ⟨⟨⟨⟨j, hj, hE⟩, h0⟩, h1⟩, h2⟩ := h
  refine ⟨⟨⟨j, hj⟩, mem_toSet.mpr hE⟩, ?_⟩
  funext i
  simp only [Finset.sum_apply, dec, Pi.zero_apply]
  rw [← Nat.cast_sum]
  fin_cases i
  · exact natCast_eq_zero_of_mod h0
  · exact natCast_eq_zero_of_mod h1
  · exact natCast_eq_zero_of_mod h2

/-- The coefficient family read off a certificate. -/
def coeffOf (N : ℕ) (cert : Cert) (E : Finset (Fin N)) : ℤ :=
  ((cert.filter fun p => decide (toSet N p.1 = E)).map Prod.snd).sum

/-- Summing `coeffOf` over the members of `S` satisfying `P`. -/
theorem sum_coeffOf {N : ℕ} (S : Finset (Finset (Fin N))) (P : Finset (Fin N) → Prop)
    {_ : DecidablePred P} (cert : Cert) (hS : ∀ p ∈ cert, toSet N p.1 ∈ S) :
    ∑ E ∈ S with P E, coeffOf N cert E =
      ((cert.filter fun p => decide (P (toSet N p.1))).map Prod.snd).sum := by
  induction cert with
  | nil => simp [coeffOf]
  | cons p L ih =>
    have hp : toSet N p.1 ∈ S := hS p (by simp)
    have hL : ∀ q ∈ L, toSet N q.1 ∈ S := fun q hq => hS q (by simp [hq])
    have hsplit : ∀ E, coeffOf N (p :: L) E =
        (if toSet N p.1 = E then p.2 else 0) + coeffOf N L E := by
      intro E
      by_cases hE : toSet N p.1 = E <;> simp [coeffOf, hE]
    simp only [hsplit, Finset.sum_add_distrib, ih hL, Finset.sum_ite_eq, Finset.mem_filter]
    by_cases hP : P (toSet N p.1) <;> simp [hP, hp]

/-- **Soundness of the checker.** -/
theorem hasIncidenceIdentity_of_check {m N t : ℕ} (f : Fin N → ℕ) (cert : DavenportCompute.Cert)
    (h : DavenportCompute.check m t (List.ofFn f) cert = true) :
    HasIncidenceIdentity ℤ (fun k => dec m (f k)) t := by
  classical
  simp only [check, List.length_ofFn, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true, beq_iff_eq, List.mem_range, List.mem_range'_1] at h
  obtain ⟨⟨⟨⟨ht2, hzero⟩, hone⟩, h1⟩, h2⟩ := h
  set u : Fin N → (Fin 3 → ZMod m) := fun k => dec m (f k)
  have hS : ∀ p ∈ cert, toSet N p.1 ∈ zeroSets u := fun p hp => by
    simpa [zeroSets] using isZeroSet_of_isZeroMask f (hzero p hp)
  refine ⟨coeffOf N cert, ?_, ?_⟩
  · have := @sum_coeffOf N (zeroSets u) (fun _ => True) (fun _ => instDecidableTrue) cert hS
    rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at this
    rw [this]
    simpa [coeffSum] using hone
  · intro J hJ1 hJt
    rw [sum_coeffOf (zeroSets u) (fun E => J ⊆ E) cert hS]
    rcases Nat.lt_or_ge 1 #J with hJ | hJ
    · -- `#J = 2`
      have h2' := h2.resolve_left (by omega)
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (show #J = 2 by omega)
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with hlt | hlt
      · simpa [coeffSum, Finset.insert_subset_iff, mem_toSet] using
          h2' x x.2 y ⟨by omega, by omega⟩
      · simpa [coeffSum, Finset.insert_subset_iff, mem_toSet, Bool.and_comm] using
          h2' y y.2 x ⟨by omega, by omega⟩
    · -- `#J = 1`
      have h1' := h1.resolve_left (by omega)
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (show #J = 1 by omega)
      simpa [coeffSum, mem_toSet] using h1' x x.2

/-! ### Long zero sets -/

theorem countP_range_eq_sum (p : ℕ → Bool) (n : ℕ) :
    (List.range n).countP p = ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, Finset.sum_range_succ, ih]
    simp [List.countP_singleton]

/-- `popcountBelow` counts the elements of `toSet`. -/
theorem card_toSet (N Z : ℕ) : #(toSet N Z) = popcountBelow N Z := by
  rw [toSet, Finset.card_filter, popcountBelow, countP_range_eq_sum,
    Fin.sum_univ_eq_sum_range (fun i => if Z.testBit i then 1 else 0)]

/-- Soundness of `longZero`. -/
theorem longZero_sound {N : ℕ} (f : Fin N → ℕ) {Z : ℕ}
    (h : DavenportCompute.longZero (List.ofFn f) Z = true) :
    IsZeroSet (fun k => dec 4 (f k)) (toSet N Z) ∧ 15 ≤ #(toSet N Z) := by
  simp only [longZero, Bool.and_eq_true, decide_eq_true_eq, List.length_ofFn] at h
  exact ⟨isZeroSet_of_isZeroMask f h.1, (card_toSet N Z).symm ▸ h.2⟩

end DavenportProject.CubeFour
