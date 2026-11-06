/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George C. Rad
-/
module

public import DavenportProject.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Codes and masks over `C_3^3`

Computational definitions shared by the two kernel-checked enumerations of Lemma 5.1: points of
`(ZMod 3)^3` as base-3 codes, bit masks of codes, and certificates of `𝓘_1`-identities
(`checkCert`, with soundness `hasIncidenceIdentity_of_checkCert`).
-/

/-!
## Computational definitions for the Lemma 5.1(2) enumeration

Points of `(ZMod 3)^3` are coded as natural numbers `n < 27` (base-3 digits).
`add3` is coordinatewise addition modulo `3` on codes and `neg3 a = add3 a a` is negation.

For a list `l` of codes (most recent first), `mk l` is the bit mask of the codes `p` that may
not be appended to `l`: bit `0`, the negatives `-q` of the entries, and the points
`-(q + r)` for pairs of distinct positions of `l`.

`checkFrom a` walks through all strictly increasing tuples `a < b < ⋯ < g` whose every entry is
admissible for its predecessors, and tests that seven such points never sum to zero while
every admissible eighth point `h > g` makes the sum zero. The kernel evaluations are in
`SupportCheck.lean`. This module holds only the definitions, so consumers that need only them (the
Lemma 5.1(1) certificates) need not wait for the kernel checks.
-/

@[expose] public section

namespace DavenportProject.CubeThree.Support

/-- Coordinatewise addition modulo `3` on base-3 codes of points of `(ZMod 3)^3`. -/
def add3 (a b : ℕ) : ℕ :=
  (a % 3 + b % 3) % 3 + 3 * ((a / 3 % 3 + b / 3 % 3) % 3) + 9 * ((a / 9 % 3 + b / 9 % 3) % 3)

/-- Negation on codes: `-x = x + x` in characteristic `3`. -/
def neg3 (a : ℕ) : ℕ := add3 a a

/-- Bits forbidden by appending `p` to the list `l`: `-p` and `-(q + p)` for `q ∈ l`. -/
def bad : List ℕ → ℕ → ℕ
  | [], p => 1 <<< neg3 p
  | q :: l, p => bad l p ||| 1 <<< neg3 (add3 q p)

/-- The mask of codes that may not be appended to `l`. -/
def mk : List ℕ → ℕ
  | [] => 1
  | p :: l => mk l ||| bad l p

/-- `allFrom s P`: the test `P k` holds for every `s ≤ k < 27`. -/
def allFrom (s : ℕ) (P : ℕ → Bool) : Bool :=
  (List.range' s (27 - s)).all P

/-- The enumeration of admissible strictly increasing tuples `a < b < ⋯ < h`,
for a fixed first point `a`. -/
def checkFrom (a : ℕ) : Bool :=
  allFrom (a + 1) fun b => (mk [a]).testBit b ||
  allFrom (b + 1) fun c => (mk [b, a]).testBit c ||
  allFrom (c + 1) fun d => (mk [c, b, a]).testBit d ||
  allFrom (d + 1) fun e => (mk [d, c, b, a]).testBit e ||
  allFrom (e + 1) fun f => (mk [e, d, c, b, a]).testBit f ||
  allFrom (f + 1) fun g => (mk [f, e, d, c, b, a]).testBit g ||
    (add3 (add3 (add3 (add3 (add3 (add3 a b) c) d) e) f) g != 0 &&
      allFrom (g + 1) fun h => (mk [g, f, e, d, c, b, a]).testBit h ||
        add3 (add3 (add3 (add3 (add3 (add3 (add3 a b) c) d) e) f) g) h == 0)

end DavenportProject.CubeThree.Support

end

/-!
## Generic lemmas for the Lemma 5.1(2) enumeration

Facts about the code arithmetic `add3`/`neg3` and the masks `mk`/`bad` that do not depend on
the kernel evaluations in `SupportCheck.lean`. The soundness theorem `enumeration` is in
`Support.lean`.
-/

public section

namespace DavenportProject.CubeThree.Support

open Finset

theorem of_allFrom {s : ℕ} {P : ℕ → Bool} (h : allFrom s P = true) {k : ℕ} (hs : s ≤ k)
    (hk : k < 27) : P k = true := by
  rw [allFrom, List.all_eq_true] at h
  exact h k (List.mem_range'_1.2 ⟨hs, by omega⟩)

theorem digits {x y z : ℕ} (hx : x < 3) (hy : y < 3) (hz : z < 3) :
    (x + 3 * y + 9 * z) % 3 = x ∧ (x + 3 * y + 9 * z) / 3 % 3 = y ∧
      (x + 3 * y + 9 * z) / 9 % 3 = z := by
  omega

theorem add3_digits (a b : ℕ) : add3 a b % 3 = (a % 3 + b % 3) % 3 ∧
    add3 a b / 3 % 3 = (a / 3 % 3 + b / 3 % 3) % 3 ∧
    add3 a b / 9 % 3 = (a / 9 % 3 + b / 9 % 3) % 3 :=
  digits (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))

theorem add3_neg3 (q : ℕ) : add3 q (neg3 q) = 0 := by
  obtain ⟨h1, h2, h3⟩ := add3_digits q q
  rw [neg3, add3]
  generalize add3 q q = r at h1 h2 h3
  omega

theorem add3_lt (a b : ℕ) : add3 a b < 27 := by
  unfold add3
  omega

theorem testBit_one_shiftLeft (n m : ℕ) : (1 <<< n).testBit m = decide (n = m) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_bad_eq_false {p h : ℕ} (h1 : h ≠ neg3 p) :
    ∀ {l : List ℕ}, (∀ q ∈ l, h ≠ neg3 (add3 q p)) → (bad l p).testBit h = false
  | [], _ => by rw [bad, testBit_one_shiftLeft]; simpa using Ne.symm h1
  | q :: l, h2 => by
    rw [bad, Nat.testBit_lor, testBit_bad_eq_false h1 fun r hr => h2 r (by simp [hr]),
      testBit_one_shiftLeft]
    simpa using Ne.symm (h2 q (by simp))

theorem testBit_mk_eq_false {h : ℕ} (h0 : h ≠ 0) :
    ∀ {l : List ℕ}, l.Nodup → (∀ q ∈ l, h ≠ neg3 q) →
      (∀ q ∈ l, ∀ r ∈ l, q ≠ r → h ≠ neg3 (add3 q r)) → (mk l).testBit h = false
  | [], _, _, _ => by
    rw [mk, show (1 : ℕ) = 1 <<< 0 from rfl, testBit_one_shiftLeft]
    simpa using Ne.symm h0
  | p :: l, hnd, h1, h2 => by
    rw [List.nodup_cons] at hnd
    rw [mk, Nat.testBit_lor,
      testBit_mk_eq_false h0 hnd.2 (fun q hq => h1 q (by simp [hq]))
        (fun q hq r hr => h2 q (by simp [hq]) r (by simp [hr])),
      testBit_bad_eq_false (h1 p (by simp))
        (fun q hq => h2 q (by simp [hq]) p (by simp) (fun e => hnd.1 (e ▸ hq)))]
    rfl

section Admissible

variable {B : Finset ℕ} (hB : ∀ n ∈ B, n < 27) (h0 : 0 ∉ B)
  (h2 : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → add3 x y ≠ 0)
  (h3 : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x ≠ y → x ≠ z → y ≠ z → add3 (add3 x y) z ≠ 0)
include h0 h2 h3

theorem testBit_mk_of_mem {l : List ℕ} {p : ℕ} (hl : ∀ q ∈ l, q ∈ B) (hnd : (p :: l).Nodup)
    (hp : p ∈ B) : (mk l).testBit p = false := by
  rw [List.nodup_cons] at hnd
  refine testBit_mk_eq_false (fun e => h0 (e ▸ hp)) hnd.2 (fun q hq e => ?_)
    (fun q hq r hr hqr e => ?_)
  · exact h2 q (hl q hq) p hp (fun e' => hnd.1 (e' ▸ hq)) (e ▸ add3_neg3 q)
  · exact h3 q (hl q hq) r (hl r hr) p hp hqr (fun e' => hnd.1 (e' ▸ hq))
      (fun e' => hnd.1 (e' ▸ hr)) (e ▸ add3_neg3 _)

end Admissible

end DavenportProject.CubeThree.Support

end

/-!
## Certificates of integral `𝓘_1`-identities for coded sequences

Points of `(ZMod 3)^3` are coded as natural numbers (base-3 digits, as in `add3`); `dec`
decodes a code. A sequence is a list `L` of codes. A *certificate* is a pair of lists
`pos`, `neg` of bit masks over the positions of `L`. `checkCert L pos neg` tests that every
mask is a nonempty zero set of `L`, that `#pos = #neg + 1`, and that every position lies in as
many masks of `pos` as of `neg`. Then the weight `+1` on the sets of `pos` and `-1` on the sets
of `neg` is an integral `𝓘_1`-identity (`hasIncidenceIdentity_of_checkCert`).

`CTree` is a binary search tree of certificates keyed by natural numbers.
-/

@[expose] public section

namespace DavenportProject.CubeThree.Identity

open Finset DavenportProject
open DavenportProject.CubeThree.Support

/-- Decoding of a base-3 code into `(ZMod 3)^3`. -/
def dec (a : ℕ) : Fin 3 → ZMod 3 := fun i => ((a / 3 ^ (i : ℕ) : ℕ) : ZMod 3)

/-- The code of the sum of the entries of `L` at the positions in the bit mask `m`. -/
def msum : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: L, m => if m % 2 = 1 then add3 a (msum L (m / 2)) else msum L (m / 2)

/-- The certificate test (see the module docstring). -/
def checkCert (L pos neg : List ℕ) : Bool :=
  pos.length == neg.length + 1 &&
    (pos ++ neg).all (fun m => msum L m == 0 && (List.range L.length).any (fun i => m.testBit i))
    && (List.range L.length).all
      (fun i => pos.countP (fun m => m.testBit i) == neg.countP (fun m => m.testBit i))

/-- A binary search tree of certificates `(pos, neg)` keyed by natural numbers. -/
inductive CTree where
  | nil : CTree
  | node : CTree → ℕ → List ℕ → List ℕ → CTree → CTree

/-- Lookup in a `CTree`. -/
def CTree.find : CTree → ℕ → Option (List ℕ × List ℕ)
  | .nil, _ => none
  | .node l k p n r, x => if x < k then l.find x else if k < x then r.find x else some (p, n)

/-- The set of positions `i < n` whose bit is set in `m`. -/
def toSet (n m : ℕ) : Finset (Fin n) := univ.filter fun i => m.testBit i

end DavenportProject.CubeThree.Identity

end

public section

namespace DavenportProject.CubeThree.Identity

open Finset DavenportProject
open DavenportProject.CubeThree.Support

theorem natCast_eq_of_mod {n m : ℕ} (h : n % 3 = m % 3) : (n : ZMod 3) = m :=
  (ZMod.natCast_eq_natCast_iff' n m 3).2 h

theorem add3_div_pow (a b : ℕ) (i : Fin 3) :
    add3 a b / 3 ^ (i : ℕ) % 3 = (a / 3 ^ (i : ℕ) + b / 3 ^ (i : ℕ)) % 3 := by
  obtain ⟨h1, h2, h3⟩ := add3_digits a b
  fin_cases i <;> simp <;> omega

theorem dec_add3 (a b : ℕ) : dec (add3 a b) = dec a + dec b := by
  ext i
  simp only [dec, Pi.add_apply]
  rw [natCast_eq_of_mod (add3_div_pow a b i)]
  push_cast
  rfl

theorem dec_zero : dec 0 = 0 := by
  ext i; simp [dec]

/-- `msum` decodes to the sum over the positions of the mask. -/
theorem dec_msum : ∀ {n : ℕ} (f : Fin n → ℕ) (m : ℕ),
    dec (msum (List.ofFn f) m) = ∑ i ∈ toSet n m, dec (f i)
  | 0, f, m => by
    rw [show toSet 0 m = ∅ from Finset.eq_empty_of_isEmpty _, sum_empty]
    simp [msum, dec_zero]
  | n + 1, f, m => by
    rw [List.ofFn_succ, msum, toSet, sum_filter, Fin.sum_univ_succ]
    have ih := dec_msum (fun i : Fin n => f i.succ) (m / 2)
    rw [toSet, sum_filter] at ih
    simp only [Fin.val_zero, Nat.testBit_zero, Fin.val_succ, Nat.testBit_succ]
    split_ifs with h h' h'
    · rw [dec_add3, ih]
    · exact absurd (by simpa using h) h'
    · exact absurd (by simpa using h') h
    · rw [ih, zero_add]

theorem isZeroSet_toSet {n : ℕ} (f : Fin n → ℕ) {m : ℕ} (h0 : msum (List.ofFn f) m = 0)
    (hne : ∃ i < n, m.testBit i = true) : IsZeroSet (fun i => dec (f i)) (toSet n m) := by
  obtain ⟨i, hi, hb⟩ := hne
  refine ⟨⟨⟨i, hi⟩, by simp [toSet, hb]⟩, ?_⟩
  rw [← dec_msum, h0, dec_zero]

/-- Counting a list of zero-set masks against the zero sets satisfying `P`. -/
theorem sum_countP {n : ℕ} (u : Fin n → (Fin 3 → ZMod 3)) (P : Finset (Fin n) → Prop)
    {_ : DecidablePred P} :
    ∀ L : List ℕ, (∀ m ∈ L, toSet n m ∈ zeroSets u) →
      ∑ E ∈ zeroSets u with P E, ((L.countP fun m => decide (toSet n m = E) : ℕ) : ℤ) =
        L.countP fun m => decide (P (toSet n m))
  | [], _ => by simp
  | m :: L, h => by
    simp only [List.countP_cons, Nat.cast_add, sum_add_distrib]
    rw [sum_countP u P L fun m' hm' => h m' (List.mem_cons_of_mem _ hm')]
    congr 1
    have hm := h m List.mem_cons_self
    by_cases hP : P (toSet n m)
    · rw [sum_eq_single_of_mem (toSet n m) (mem_filter.2 ⟨hm, hP⟩)]
      · simp [hP]
      · intro E _ hE
        simp [Ne.symm hE]
    · rw [sum_eq_zero]
      · simp [hP]
      · intro E hE
        have : toSet n m ≠ E := fun e => hP (e ▸ (mem_filter.1 hE).2)
        simp [this]

theorem mem_toSet {n m : ℕ} (i : Fin n) : i ∈ toSet n m ↔ m.testBit i = true := by
  simp [toSet]

/-- Soundness of `checkCert`. -/
theorem hasIncidenceIdentity_of_checkCert {n : ℕ} (f : Fin n → ℕ) {pos neg : List ℕ}
    (h : checkCert (List.ofFn f) pos neg = true) :
    HasIncidenceIdentity ℤ (fun i => dec (f i)) 1 := by
  simp only [checkCert, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range, List.length_ofFn] at h
  obtain ⟨⟨hlen, hall⟩, hmom⟩ := h
  set u := fun i => dec (f i)
  have hZ : ∀ m ∈ pos ++ neg, toSet n m ∈ zeroSets u := by
    intro m hm
    obtain ⟨h0, i, hi, hb⟩ := hall m hm
    rw [DavenportProject.mem_zeroSets]
    exact isZeroSet_toSet f h0 ⟨i, hi, hb⟩
  have hP : ∀ m ∈ pos, toSet n m ∈ zeroSets u := fun m hm => hZ m (List.mem_append_left _ hm)
  have hN : ∀ m ∈ neg, toSet n m ∈ zeroSets u := fun m hm => hZ m (List.mem_append_right _ hm)
  refine ⟨fun E => ((pos.countP fun m => decide (toSet n m = E) : ℕ) : ℤ) -
    ((neg.countP fun m => decide (toSet n m = E) : ℕ) : ℤ), ?_, ?_⟩
  · have h1 := @sum_countP n u (fun _ => True) (fun _ => instDecidableTrue) pos hP
    have h2 := @sum_countP n u (fun _ => True) (fun _ => instDecidableTrue) neg hN
    simp only [filter_true_of_mem (fun _ _ => trivial), decide_true, List.countP_true] at h1 h2
    rw [sum_sub_distrib, h1, h2, hlen]
    push_cast; ring
  · intro J hJ1 hJ2
    obtain ⟨i, rfl⟩ := card_eq_one.1 (le_antisymm hJ2 hJ1)
    rw [sum_sub_distrib, sum_countP u _ pos hP, sum_countP u _ neg hN]
    simp only [singleton_subset_iff, mem_toSet, Bool.decide_eq_true]
    rw [hmom i i.isLt, sub_self]

end DavenportProject.CubeThree.Identity

end
