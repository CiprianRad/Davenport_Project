/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George C. Rad
-/
module

public import DavenportProject.Bases.CubeThree.IdentityData
import Mathlib.Tactic.IntervalCases

/-!
# Kernel check for Lemma 5.1(1)

The finite enumeration behind Lemma 5.1(1), evaluated by the kernel (`decide +kernel`).
-/

/-!
## Kernel-checked enumeration for Lemma 5.1(1)

A normalized case is a non-decreasing list of ten codes `1, 1, 3, 3, a₄, …, a₉`
(`1 = e₁`, `3 = e₂`, `9 = e₃`) of a sequence without zero sets of size at most three.
`skip l b` (with `l` the codes chosen so far, most recent first) is `true` when appending `b`
is excluded:
* `9` would be skipped (`p < 9 < b` for the last code `p`), or
* `b` would be a third copy of the last code, or
* `b` is new and lies in the mask `mk l` of codes that complete a zero set of size at most
  three with the entries of `l` (or is `0`).

`tail a₄` walks through all such lists with fourth entry `a₄` and tests at each leaf the
certificate stored in `certTree` under `key l`. It is evaluated by the kernel
(`decide +kernel`), one declaration per value of `a₄`.
-/

@[expose] public section

namespace DavenportProject.CubeThree.Identity

open DavenportProject.CubeThree.Support

/-- Appending `b` to the codes `l` (most recent first) is excluded. -/
def skip : List ℕ → ℕ → Bool
  | p :: p2 :: l, b => (decide (p < 9) && decide (9 < b)) ||
      (if b == p then p2 == b else (mk (p :: p2 :: l)).testBit b)
  | _, _ => true

/-- The key of a case in `certTree`. -/
def key : List ℕ → ℕ
  | [] => 0
  | a :: l => a + 27 * key l

/-- The certificate test at a leaf `l` (most recent first). -/
def leaf (l : List ℕ) : Bool :=
  match certTree.find (key l) with
  | some (p, n) => checkCert l.reverse p n
  | none => false

/-- The last five levels of the enumeration, for fixed `a₄` and `a₅`. -/
def tail5 (a4 a5 : ℕ) : Bool :=
  skip [a4, 3, 3, 1, 1] a5 ||
  allFrom a5 fun a6 => skip [a5, a4, 3, 3, 1, 1] a6 ||
  allFrom a6 fun a7 => skip [a6, a5, a4, 3, 3, 1, 1] a7 ||
  allFrom a7 fun a8 => skip [a7, a6, a5, a4, 3, 3, 1, 1] a8 ||
  allFrom a8 fun a9 => skip [a8, a7, a6, a5, a4, 3, 3, 1, 1] a9 ||
    leaf [a9, a8, a7, a6, a5, a4, 3, 3, 1, 1]

/-- The enumeration for a fixed `a₄`. -/
def tail4 (a4 : ℕ) : Bool :=
  skip [3, 3, 1, 1] a4 || allFrom a4 fun a5 => tail5 a4 a5

/-! The kernel evaluates one value of `a₄` per declaration. Declarations are checked one after
another (`Elab.async false`), so that at most one kernel evaluation (at most about 2.5 GB, for
`a₄ = 9`) is alive at a time. -/

set_option Elab.async false

theorem tail4_3 : tail4 3 = true := by decide +kernel
theorem tail4_4 : tail4 4 = true := by decide +kernel
theorem tail4_5 : tail4 5 = true := by decide +kernel
theorem tail4_6 : tail4 6 = true := by decide +kernel
theorem tail4_7 : tail4 7 = true := by decide +kernel
theorem tail4_8 : tail4 8 = true := by decide +kernel
theorem tail4_9 : tail4 9 = true := by decide +kernel
theorem tail4_10 : tail4 10 = true := by decide +kernel
theorem tail4_11 : tail4 11 = true := by decide +kernel
theorem tail4_12 : tail4 12 = true := by decide +kernel
theorem tail4_13 : tail4 13 = true := by decide +kernel
theorem tail4_14 : tail4 14 = true := by decide +kernel
theorem tail4_15 : tail4 15 = true := by decide +kernel
theorem tail4_16 : tail4 16 = true := by decide +kernel
theorem tail4_17 : tail4 17 = true := by decide +kernel
theorem tail4_18 : tail4 18 = true := by decide +kernel
theorem tail4_19 : tail4 19 = true := by decide +kernel
theorem tail4_20 : tail4 20 = true := by decide +kernel
theorem tail4_21 : tail4 21 = true := by decide +kernel
theorem tail4_22 : tail4 22 = true := by decide +kernel
theorem tail4_23 : tail4 23 = true := by decide +kernel
theorem tail4_24 : tail4 24 = true := by decide +kernel
theorem tail4_25 : tail4 25 = true := by decide +kernel
theorem tail4_26 : tail4 26 = true := by decide +kernel

theorem tail4_eq_true {a : ℕ} (h3 : 3 ≤ a) (h27 : a < 27) : tail4 a = true := by
  interval_cases a
  exacts [tail4_3, tail4_4, tail4_5, tail4_6, tail4_7, tail4_8, tail4_9, tail4_10, tail4_11,
    tail4_12, tail4_13, tail4_14, tail4_15, tail4_16, tail4_17, tail4_18, tail4_19, tail4_20,
    tail4_21, tail4_22, tail4_23, tail4_24, tail4_25, tail4_26]

end DavenportProject.CubeThree.Identity

end
