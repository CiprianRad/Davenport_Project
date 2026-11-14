/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportCompute.Search
public import DavenportProject.Bases.CubeFour.Codes
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring

/-!
# Soundness of the certificate checker of the kernel enumeration

The kernel enumeration of Lemma 5.3 (`DavenportCompute.Search`) checks the certificates of integral
`𝓘_t`-identities with `checkEntries`, which replaces the lists of masks of
`DavenportCompute.check` by sums of `24`-bit slots. This file shows that `checkEntries` implies
`check`, whose soundness is `hasIncidenceIdentity_of_check`.

* `toCert es`: the entries `2 E` and `2 E + 1` of `es` as the masks `E` with the coefficients `1`
  and `-1`.
* `spread_eq`, `spreadWide_eq`, `spread_mul_spreadWide`, `vec_eq`: the numbers built by table
  lookups and by `vec`, as sums over slots.
* `sum_mul_pow_div_pow_mod`: the digits of `∑ a s * b ^ s` with `a s < b`. A slot of a signed sum
  `sumSign` counts entries, and there are fewer than `2 ^ 24` of them, so equal signed sums have
  equal slots (`sumSign_eq_of_sum`): these are the moments of degree one and two.
* `slot_spread_mul_vec`: the slot `N - 1` of `spread E * vec q N` is `D₀ + 64 D₁ + 4096 D₂`, with
  `Dᵢ ≤ 54` the sum of the digits `i` of the codes at the positions in `E`; hence
  `isZeroMask_of_zeroMask`.
* `check_of_checkEntries`, `hasIncidenceIdentity_of_checkEntries`: the soundness of
  `checkEntries`.
-/

@[expose] public section

namespace DavenportProject.CubeFour

open Finset DavenportCompute DavenportCompute.Search

/-! ## Base-`b` digits -/

/-- A sum `∑ a s * b ^ s` with digits `a s < b` has the digit `a m` at the place `m`. -/
theorem sum_mul_pow_div_pow_mod {b S : ℕ} {a : ℕ → ℕ} (ha : ∀ s < S, a s < b) {m : ℕ} (hm : m < S) :
    (∑ s ∈ range S, a s * b ^ s) / b ^ m % b = a m := by
  induction S generalizing a m with
  | zero => omega
  | succ S ih =>
    have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) (ha 0 (by omega))
    have hsum : ∑ s ∈ range (S + 1), a s * b ^ s =
        a 0 + b * ∑ s ∈ range S, a (s + 1) * b ^ s := by
      rw [sum_range_succ', mul_sum, add_comm, pow_zero, mul_one]
      congr 1
      exact sum_congr rfl fun s _ => by ring
    rw [hsum]
    rcases m with _ | m
    · rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ha 0 (by omega))]
    · rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hb,
        Nat.div_eq_of_lt (ha 0 (by omega)), zero_add]
      exact ih (fun s hs => ha (s + 1) (by omega)) (by omega)

/-- Two sums `∑ a s * b ^ s` with digits below `b` agree only if their digits do. -/
theorem eq_of_sum_mul_pow_eq {b S : ℕ} {a a' : ℕ → ℕ} (ha : ∀ s < S, a s < b)
    (ha' : ∀ s < S, a' s < b)
    (h : ∑ s ∈ range S, a s * b ^ s = ∑ s ∈ range S, a' s * b ^ s) {m : ℕ} (hm : m < S) :
    a m = a' m := by
  rw [← sum_mul_pow_div_pow_mod ha hm, ← sum_mul_pow_div_pow_mod ha' hm, h]

/-! ## Signed sums over the entries -/

theorem sumSign_nil (b : ℕ) (f : ℕ → ℕ) : sumSign b f [] = 0 := rfl

/-- One more entry: it counts when its last bit is `b`. -/
theorem sumSign_cons (b : ℕ) (f : ℕ → ℕ) (e : ℕ) (es : List ℕ) :
    sumSign b f (e :: es) = sumSign b f es + if e % 2 = b then f (e / 2) else 0 := by
  have h1 : Nat.land e 1 = e % 2 := Nat.and_one_is_mod e
  have h2 : Nat.shiftRight e 1 = e / 2 := Nat.shiftRight_eq_div_pow e 1
  change cond (Nat.beq (Nat.land e 1) b) (Nat.add (sumSign b f es) (f (Nat.shiftRight e 1)))
    (sumSign b f es) = _
  rw [h1, h2]
  rcases Bool.eq_false_or_eq_true (Nat.beq (e % 2) b) with hb | hb
  · rw [hb]
    simp [Nat.eq_of_beq_eq_true hb]
  · rw [hb]
    simp [Nat.ne_of_beq_eq_false hb]

/-- `sumSign` is linear in the place values. -/
theorem sumSign_sum (b B S : ℕ) (g : ℕ → ℕ → ℕ) (es : List ℕ) :
    sumSign b (fun E => ∑ s ∈ range S, g s E * B ^ s) es =
      ∑ s ∈ range S, sumSign b (g s) es * B ^ s := by
  induction es with
  | nil => simp [sumSign_nil]
  | cons e es ih =>
    simp only [sumSign_cons, ih, add_mul, sum_add_distrib]
    congr 1
    split_ifs <;> simp

theorem ite_one_zero_le (p : Prop) [Decidable p] : (if p then 1 else 0 : ℕ) ≤ 1 := by
  split_ifs <;> omega

/-- A signed count is at most the number of entries. -/
theorem sumSign_le (b : ℕ) {f : ℕ → ℕ} (hf : ∀ E, f E ≤ 1) (es : List ℕ) :
    sumSign b f es ≤ es.length := by
  induction es with
  | nil => simp [sumSign_nil]
  | cons e es ih =>
    have := hf (e / 2)
    rw [sumSign_cons, List.length_cons]
    split_ifs <;> omega

/-- Equal signed sums of `∑ g s E * 2 ^ (24 s)` with `g s E ≤ 1`, over fewer than `2 ^ 24`
entries, have equal signed sums of every `g s`. -/
theorem sumSign_eq_of_sum {S : ℕ} {g : ℕ → ℕ → ℕ} (hg : ∀ s E, g s E ≤ 1) {es : List ℕ}
    (hlen : es.length < 2 ^ 24)
    (h : sumSign 0 (fun E => ∑ s ∈ range S, g s E * (2 ^ 24) ^ s) es =
      sumSign 1 (fun E => ∑ s ∈ range S, g s E * (2 ^ 24) ^ s) es) {s : ℕ} (hs : s < S) :
    sumSign 0 (g s) es = sumSign 1 (g s) es := by
  rw [sumSign_sum, sumSign_sum] at h
  exact eq_of_sum_mul_pow_eq (fun s _ => lt_of_le_of_lt (sumSign_le 0 (hg s) es) hlen)
    (fun s _ => lt_of_le_of_lt (sumSign_le 1 (hg s) es) hlen) h hs

/-- The certificate entries `2 E` (coefficient `1`) and `2 E + 1` (coefficient `-1`) as a
certificate of `DavenportCompute.check`. -/
def toCert (es : List ℕ) : DavenportCompute.Cert :=
  es.map fun e => (e / 2, if e % 2 = 1 then -1 else 1)

/-- The coefficient sums of `toCert es` are differences of signed counts. -/
theorem coeffSum_toCert (P : ℕ → Bool) (es : List ℕ) :
    coeffSum P (toCert es) = (sumSign 0 (fun E => if P E then 1 else 0) es : ℤ) -
      sumSign 1 (fun E => if P E then 1 else 0) es := by
  induction es with
  | nil => simp [coeffSum, toCert, sumSign_nil]
  | cons e es ih =>
    have hc : coeffSum P (toCert (e :: es)) =
        (if P (e / 2) then (if e % 2 = 1 then -1 else 1) else 0) + coeffSum P (toCert es) := by
      simp only [coeffSum, toCert, List.map_cons, List.filter_cons]
      split_ifs <;> simp
    rw [hc, ih, sumSign_cons, sumSign_cons]
    rcases Nat.mod_two_eq_zero_or_one e with h | h <;> cases P (e / 2) <;> simp [h] <;> ring

/-! ## Table lookups -/

/-- The piece of `T24` for the six-bit mask `m`. -/
def lo24 (m : ℕ) : ℕ := Nat.land (Nat.shiftRight T24 (Nat.mul 144 m)) ((1 <<< 144) - 1)

/-- The piece of `T432` for the six-bit mask `m`. -/
def lo432 (m : ℕ) : ℕ := Nat.land (Nat.shiftRight T432 (Nat.mul 2592 m)) ((1 <<< 2592) - 1)

/-- The table `T24`, checked by the kernel. -/
theorem lo24_eq : ∀ m < 64,
    lo24 m = ∑ j ∈ range 6, (if m.testBit j then 1 else 0) * (2 ^ 24) ^ j := by
  decide +kernel

/-- The table `T432`, checked by the kernel. -/
theorem lo432_eq : ∀ m < 64,
    lo432 m = ∑ j ∈ range 6, (if m.testBit j then 1 else 0) * ((2 ^ 24) ^ 18) ^ j := by
  decide +kernel

theorem shiftLeft_mul_eq (a m n : ℕ) : a <<< (m * n) = a * (2 ^ m) ^ n := by
  rw [Nat.shiftLeft_eq, pow_mul]

/-- `spread` in terms of the pieces of `T24` for the three six-bit pieces of `E`. -/
theorem spread_eq_lo (E : ℕ) : spread E = lo24 (E % 2 ^ 6) +
    (lo24 (E / 2 ^ 6 % 2 ^ 6) * (2 ^ 24) ^ 6 + lo24 (E / 2 ^ 12 % 2 ^ 6) * (2 ^ 24) ^ 12) := by
  have h0 : Nat.land E 63 = E % 2 ^ 6 := Nat.and_two_pow_sub_one_eq_mod E 6
  have h1 : Nat.land (Nat.shiftRight E 6) 63 = E / 2 ^ 6 % 2 ^ 6 := by
    rw [← Nat.shiftRight_eq_div_pow]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
  have h2 : Nat.land (Nat.shiftRight E 12) 63 = E / 2 ^ 12 % 2 ^ 6 := by
    rw [← Nat.shiftRight_eq_div_pow]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
  change lo24 (Nat.land E 63) + (lo24 (Nat.land (Nat.shiftRight E 6) 63) <<< (24 * 6) +
    lo24 (Nat.land (Nat.shiftRight E 12) 63) <<< (24 * 12)) = _
  rw [h0, h1, h2, shiftLeft_mul_eq, shiftLeft_mul_eq]

/-- `spreadWide` in terms of the pieces of `T432` for the three six-bit pieces of `E`. -/
theorem spreadWide_eq_lo (E : ℕ) : spreadWide E = lo432 (E % 2 ^ 6) +
    (lo432 (E / 2 ^ 6 % 2 ^ 6) * ((2 ^ 24) ^ 18) ^ 6 +
      lo432 (E / 2 ^ 12 % 2 ^ 6) * ((2 ^ 24) ^ 18) ^ 12) := by
  have h0 : Nat.land E 63 = E % 2 ^ 6 := Nat.and_two_pow_sub_one_eq_mod E 6
  have h1 : Nat.land (Nat.shiftRight E 6) 63 = E / 2 ^ 6 % 2 ^ 6 := by
    rw [← Nat.shiftRight_eq_div_pow]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
  have h2 : Nat.land (Nat.shiftRight E 12) 63 = E / 2 ^ 12 % 2 ^ 6 := by
    rw [← Nat.shiftRight_eq_div_pow]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
  change lo432 (Nat.land E 63) + (lo432 (Nat.land (Nat.shiftRight E 6) 63) <<< (24 * 18 * 6) +
    lo432 (Nat.land (Nat.shiftRight E 12) 63) <<< (24 * 18 * 12)) = _
  rw [h0, h1, h2, shiftLeft_mul_eq, shiftLeft_mul_eq, pow_mul]

/-- Splitting eighteen bits into three pieces of six bits. -/
theorem sum_eighteen (E w : ℕ) (L : ℕ → ℕ) (hL : ∀ m < 64,
    L m = ∑ j ∈ range 6, (if m.testBit j then 1 else 0) * w ^ j) :
    L (E % 2 ^ 6) + (L (E / 2 ^ 6 % 2 ^ 6) * w ^ 6 + L (E / 2 ^ 12 % 2 ^ 6) * w ^ 12) =
      ∑ j ∈ range 18, (if E.testBit j then 1 else 0) * w ^ j := by
  have hm : ∀ n, n % 2 ^ 6 < 64 := fun n => Nat.mod_lt _ (by norm_num)
  rw [hL _ (hm _), hL _ (hm _), hL _ (hm _), show 18 = 6 + 6 + 6 from rfl, sum_range_add,
    sum_range_add, sum_mul, sum_mul, add_assoc]
  refine congrArg₂ (· + ·) ?_ (congrArg₂ (· + ·) ?_ ?_) <;>
    refine sum_congr rfl fun j hj => ?_ <;> have hj6 : j < 6 := mem_range.mp hj
  · rw [Nat.testBit_mod_two_pow, decide_eq_true hj6, Bool.true_and]
  · rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, decide_eq_true hj6, Bool.true_and,
      add_comm j 6, pow_add]
    ring
  · rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, decide_eq_true hj6, Bool.true_and,
      show 6 + 6 + j = j + 12 by omega, pow_add]
    ring

/-- `spread E = ∑_{j < 18, j ∈ E} 2 ^ (24 j)`. -/
theorem spread_eq (E : ℕ) :
    spread E = ∑ j ∈ range 18, (if E.testBit j then 1 else 0) * (2 ^ 24) ^ j := by
  rw [spread_eq_lo, ← sum_eighteen E (2 ^ 24) lo24 lo24_eq]

/-- `spreadWide E = ∑_{k < 18, k ∈ E} 2 ^ (432 k)`. -/
theorem spreadWide_eq (E : ℕ) :
    spreadWide E = ∑ k ∈ range 18, (if E.testBit k then 1 else 0) * ((2 ^ 24) ^ 18) ^ k := by
  rw [spreadWide_eq_lo, ← sum_eighteen E ((2 ^ 24) ^ 18) lo432 lo432_eq]

/-- A sum over `s < m n` as a double sum over `s = m k + j`. -/
theorem sum_range_mul_eq (f : ℕ → ℕ) (m n : ℕ) :
    ∑ s ∈ range (m * n), f s = ∑ k ∈ range n, ∑ j ∈ range m, f (m * k + j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

theorem ite_and_eq_mul (a b : Bool) : (if (a && b) = true then 1 else 0 : ℕ) =
    (if a = true then 1 else 0) * (if b = true then 1 else 0) := by
  cases a <;> cases b <;> rfl

/-- `spread E * spreadWide E` has the slot `j + 18 k` for the pair `(j, k)` of positions of
`E`. -/
theorem spread_mul_spreadWide (E : ℕ) :
    Nat.mul (spread E) (spreadWide E) = ∑ s ∈ range 324,
      (if E.testBit (s % 18) && E.testBit (s / 18) then 1 else 0) * (2 ^ 24) ^ s := by
  change spread E * spreadWide E = _
  rw [spread_eq, spreadWide_eq, sum_mul_sum, sum_comm, show 324 = 18 * 18 from rfl,
    sum_range_mul_eq]
  refine sum_congr rfl fun k _ => sum_congr rfl fun j hj => ?_
  have hj' : j < 18 := mem_range.mp hj
  have hp : ((2 : ℕ) ^ 24) ^ (18 * k + j) = (2 ^ 24) ^ j * ((2 ^ 24) ^ 18) ^ k := by
    rw [pow_add, pow_mul, mul_comm]
  rw [show (18 * k + j) % 18 = j by omega, show (18 * k + j) / 18 = k by omega, hp, ite_and_eq_mul]
  ring

/-- `vec q n = ∑_{i < n} val (code i) * 2 ^ (24 i)`. -/
theorem vec_eq (q n : ℕ) :
    vec q n = ∑ i ∈ range n, Search.val (q / 64 ^ i % 64) * (2 ^ 24) ^ i := by
  induction n with
  | zero => simp [vec]
  | succ n ih =>
    rw [sum_range_succ, ← ih]
    change vec q n + Search.val ((q >>> (6 * n)) &&& 63) <<< (24 * n) = _
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, show (63 : ℕ) = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, pow_mul, pow_mul]
    norm_num

/-! ## Zero sets: the slot `N - 1` of `spread E * vec q N` -/

/-- The three base-`4` digits of a code in the six-bit fields of `val`. -/
theorem val_eq_digits : ∀ a < 64,
    Search.val a = digit 4 a 0 + 64 * digit 4 a 1 + 4096 * digit 4 a 2 := by
  decide +kernel

theorem digit_four_lt (a i : ℕ) : digit 4 a i < 4 := Nat.mod_lt _ (by norm_num)

theorem val_le_of_lt {a : ℕ} (ha : a < 64) : Search.val a ≤ 12483 := by
  have := digit_four_lt a 0
  have := digit_four_lt a 1
  have := digit_four_lt a 2
  rw [val_eq_digits a ha]
  omega

/-- The code at position `j`, or `0` beyond the end. -/
def codeAt {N : ℕ} (c : Fin N → ℕ) (j : ℕ) : ℕ := if h : j < N then c ⟨j, h⟩ else 0

theorem codeAt_lt {N : ℕ} {c : Fin N → ℕ} (hc : ∀ i, c i < 64) (j : ℕ) : codeAt c j < 64 := by
  unfold codeAt
  split_ifs
  exacts [hc _, by norm_num]

/-- The product of two sums in base `b`, as a sum in base `b`. -/
theorem sum_mul_sum_pow (b n : ℕ) (x u : ℕ → ℕ) :
    (∑ j ∈ range n, x j * b ^ j) * (∑ i ∈ range n, u i * b ^ i) =
      ∑ s ∈ range (n + n),
        (∑ j ∈ range n, ∑ i ∈ range n, if j + i = s then x j * u i else 0) * b ^ s := by
  rw [sum_mul_sum]
  symm
  simp only [sum_mul]
  conv_lhs => rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  conv_lhs => rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  have hji : j + i ∈ range (n + n) := by
    rw [mem_range] at hj hi ⊢
    omega
  simp only [ite_mul, zero_mul, sum_ite_eq, hji, ↓reduceIte]
  ring

/-- The slot `N - 1` of `spread E * vec q N` is `∑_{k ∈ E} val (c k)`. -/
theorem slot_spread_mul_vec {N q : ℕ} (c : Fin N → ℕ) (hc : ∀ i, c i < 64)
    (hq : ∀ i : Fin N, q / 64 ^ (N - 1 - i) % 64 = c i) (hN : N ≤ 18) {E : ℕ}
    (hE : ∀ j, N ≤ j → E.testBit j = false) (hN1 : 1 ≤ N) :
    spread E * vec q N / (2 ^ 24) ^ (N - 1) % 2 ^ 24 = ∑ k ∈ toSet N E, Search.val (c k) := by
  have hspread : spread E = ∑ j ∈ range N, (if E.testBit j then 1 else 0) * (2 ^ 24) ^ j := by
    obtain ⟨r, hr⟩ : ∃ r, 18 = N + r := ⟨18 - N, by omega⟩
    have h0 : ∑ j ∈ range r, (if E.testBit (N + j) then 1 else 0) * (2 ^ 24) ^ (N + j) = 0 :=
      sum_eq_zero fun j _ => by rw [hE (N + j) (by omega)]; simp
    rw [spread_eq, hr, sum_range_add, h0, add_zero]
  have hvec : vec q N = ∑ i ∈ range N, Search.val (codeAt c (N - 1 - i)) * (2 ^ 24) ^ i := by
    rw [vec_eq]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i < N := mem_range.mp hi
    have h1 : N - 1 - i < N := by omega
    have h2 := hq ⟨N - 1 - i, h1⟩
    rw [Fin.val_mk, show N - 1 - (N - 1 - i) = i by omega] at h2
    rw [h2, codeAt, dite_eq_left h1]
  have hX : spread E * vec q N = ∑ s ∈ range (N + N), (∑ j ∈ range N, ∑ i ∈ range N,
      if j + i = s then (if E.testBit j then 1 else 0) * Search.val (codeAt c (N - 1 - i))
        else 0) * (2 ^ 24) ^ s := by
    rw [hspread, hvec]
    exact sum_mul_sum_pow _ _ _ _
  rw [hX, sum_mul_pow_div_pow_mod _ (by omega)]
  · rw [toSet, sum_filter, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun k _ => ?_
    have hk := k.2
    rw [sum_eq_single (N - 1 - k)]
    · rw [ite_eq_left (by omega), show N - 1 - (N - 1 - (k : ℕ)) = k by omega, codeAt,
        dite_eq_left hk]
      split_ifs <;> simp
    · intro i _ hi
      rw [ite_eq_right (by omega)]
    · intro hn
      exact absurd (mem_range.mpr (by omega)) hn
  · intro s _
    calc _ ≤ ∑ j ∈ range N, ∑ i ∈ range N, 12483 := by
          refine sum_le_sum fun j _ => sum_le_sum fun i _ => ?_
          have := val_le_of_lt (codeAt_lt hc (N - 1 - i))
          split_ifs <;> omega
      _ = N * (N * 12483) := by simp
      _ ≤ 18 * (18 * 12483) := Nat.mul_le_mul hN (Nat.mul_le_mul_right _ hN)
      _ < 2 ^ 24 := by norm_num

/-- A mask accepted by `zeroMask` is accepted by `isZeroMask`. -/
theorem isZeroMask_of_zeroMask {N q : ℕ} (c : Fin N → ℕ) (hc : ∀ i, c i < 64)
    (hq : ∀ i : Fin N, q / 64 ^ (N - 1 - i) % 64 = c i) (hN : N ≤ 18) {E : ℕ}
    (h : zeroMask N (vec q N) E = true) : isZeroMask 4 (List.ofFn c) E = true := by
  simp only [zeroMask, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at h
  obtain ⟨⟨hE0, hEN⟩, hY⟩ := h
  have hE0' : E ≠ 0 := Nat.ne_of_beq_eq_false hE0
  have hEN' : E < 2 ^ N := by
    have h1 : E / 2 ^ N = 0 := (Nat.shiftRight_eq_div_pow E N).symm.trans hEN
    rcases Nat.lt_or_ge E (2 ^ N) with h2 | h2
    · exact h2
    · have := Nat.div_pos h2 (Nat.two_pow_pos N)
      omega
  have hE : ∀ j, N ≤ j → E.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hEN' (Nat.pow_le_pow_right (by norm_num) hj))
  obtain ⟨j₀, hj₀⟩ := Nat.exists_testBit_of_ne_zero hE0'
  have hj₀N : j₀ < N := by
    by_contra hcon
    rw [hE j₀ (by omega)] at hj₀
    exact Bool.false_ne_true hj₀
  have hslot := slot_spread_mul_vec c hc hq hN hE (by omega)
  have hY' : ((spread E * vec q N) >>> (24 * (N - 1))) &&& 12483 = 0 := hY
  rw [Nat.shiftRight_eq_div_pow, pow_mul] at hY'
  set Y := spread E * vec q N / (2 ^ 24) ^ (N - 1)
  have hb : ∀ i, (12483 : ℕ).testBit i = true → ¬(Y / 2 ^ i % 2 = 1) := by
    intro i hi
    have h2 := congrArg (fun z => z.testBit i) hY'
    simp only [Nat.testBit_and, hi, Bool.and_true, Nat.zero_testBit] at h2
    rw [Nat.testBit_eq_decide_div_mod_eq] at h2
    exact of_decide_eq_false h2
  have k0 := hb 0 (by decide)
  have k1 := hb 1 (by decide)
  have k6 := hb 6 (by decide)
  have k7 := hb 7 (by decide)
  have k12 := hb 12 (by decide)
  have k13 := hb 13 (by decide)
  simp only [Nat.reducePow, Nat.div_one] at k0 k1 k6 k7 k12 k13 hslot
  have hval : ∑ k ∈ toSet N E, Search.val (c k) = ∑ k ∈ toSet N E, digit 4 (c k) 0 +
      64 * ∑ k ∈ toSet N E, digit 4 (c k) 1 + 4096 * ∑ k ∈ toSet N E, digit 4 (c k) 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => val_eq_digits _ (hc k)
  have hD : ∀ i, ∑ k ∈ toSet N E, digit 4 (c k) i ≤ 54 := by
    intro i
    calc _ ≤ ∑ k ∈ toSet N E, 3 := sum_le_sum fun k _ => by have := digit_four_lt (c k) i; omega
      _ = #(toSet N E) * 3 := by simp
      _ ≤ N * 3 := Nat.mul_le_mul_right _ ((card_filter_le _ _).trans (by simp))
      _ ≤ 54 := by omega
  have hD0 := hD 0
  have hD1 := hD 1
  have hD2 := hD 2
  simp only [isZeroMask, Bool.and_eq_true, List.any_eq_true, List.mem_range, List.length_ofFn,
    beq_iff_eq, maskSum_ofFn_eq_sum]
  refine ⟨⟨⟨⟨j₀, hj₀N, hj₀⟩, ?_⟩, ?_⟩, ?_⟩ <;> omega

/-! ## The certificate checker -/

/-- A certificate accepted by `checkEntries` gives a certificate accepted by
`DavenportCompute.check`. -/
theorem check_of_checkEntries {N t q : ℕ} (c : Fin N → ℕ) (hc : ∀ i, c i < 64)
    (hq : ∀ i : Fin N, q / 64 ^ (N - 1 - i) % 64 = c i) (ht : t = 1 ∨ t = 2) (es : List ℕ)
    (h : DavenportCompute.Search.checkEntries N t q es = true) :
    DavenportCompute.check 4 t (List.ofFn c) (toCert es) = true := by
  simp only [checkEntries, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hN, hlen⟩, hzero⟩, hone⟩, hmom⟩ := h
  have hlen' : es.length < 2 ^ 24 := by norm_num; omega
  have hmom' : (∀ j < 18, sumSign 0 (fun E => if E.testBit j then 1 else 0) es =
      sumSign 1 (fun E => if E.testBit j then 1 else 0) es) ∧
      (t = 2 → ∀ j < 18, ∀ k < 18,
        sumSign 0 (fun E => if (E.testBit j && E.testBit k) then 1 else 0) es =
          sumSign 1 (fun E => if (E.testBit j && E.testBit k) then 1 else 0) es) := by
    rcases ht with rfl | rfl
    · change Nat.beq (sumSign 0 spread es) (sumSign 1 spread es) = true at hmom
      rw [Nat.beq_eq, show spread = fun E => ∑ j ∈ range 18,
        (if E.testBit j then 1 else 0) * (2 ^ 24) ^ j from funext spread_eq] at hmom
      exact ⟨fun j hj => sumSign_eq_of_sum (g := fun j E => if E.testBit j then 1 else 0)
        (fun _ _ => ite_one_zero_le _) hlen' hmom hj, fun h => absurd h (by norm_num)⟩
    · change Nat.beq (sumSign 0 (fun E => Nat.mul (spread E) (spreadWide E)) es)
        (sumSign 1 (fun E => Nat.mul (spread E) (spreadWide E)) es) = true at hmom
      rw [Nat.beq_eq] at hmom
      simp only [spread_mul_spreadWide] at hmom
      have hp : ∀ j < 18, ∀ k < 18,
          sumSign 0 (fun E => if (E.testBit j && E.testBit k) then 1 else 0) es =
            sumSign 1 (fun E => if (E.testBit j && E.testBit k) then 1 else 0) es := by
        intro j hj k hk
        have := sumSign_eq_of_sum
          (g := fun s E => if (E.testBit (s % 18) && E.testBit (s / 18)) then 1 else 0)
          (fun _ _ => ite_one_zero_le _) hlen' hmom (show 18 * k + j < 324 by omega)
        simpa only [show (18 * k + j) % 18 = j by omega, show (18 * k + j) / 18 = k by omega]
          using this
      exact ⟨fun j hj => by simpa only [Bool.and_self] using hp j hj j hj, fun _ => hp⟩
  obtain ⟨h1, h2⟩ := hmom'
  simp only [check, List.length_ofFn, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true, beq_iff_eq, List.mem_range, List.mem_range'_1, coeffSum_toCert]
  refine ⟨⟨⟨⟨by omega, ?_⟩, ?_⟩, Or.inr fun j hj => ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    have := hzero e he
    rw [show Nat.shiftRight e 1 = e / 2 from Nat.shiftRight_eq_div_pow e 1] at this
    exact isZeroMask_of_zeroMask c hc hq hN this
  · simp only [Nat.succ_eq_add_one] at hone
    simp only [ite_true]
    omega
  · rw [h1 j (by omega), sub_self]
  · rcases ht with rfl | rfl
    · exact Or.inl (by norm_num)
    · refine Or.inr fun j hj k hk => ?_
      have := h2 rfl j (by omega) k (by omega)
      simp only [Bool.and_eq_true] at this
      rw [this, sub_self]

/-- **Soundness of `checkEntries`.** -/
theorem hasIncidenceIdentity_of_checkEntries {N t q : ℕ} (c : Fin N → ℕ) (hc : ∀ i, c i < 64)
    (hq : ∀ i : Fin N, q / 64 ^ (N - 1 - i) % 64 = c i) (ht : t = 1 ∨ t = 2) (es : List ℕ)
    (h : DavenportCompute.Search.checkEntries N t q es = true) :
    HasIncidenceIdentity ℤ (fun k => dec 4 (c k)) t :=
  hasIncidenceIdentity_of_check c _ (check_of_checkEntries c hc hq ht es h)

end DavenportProject.CubeFour
