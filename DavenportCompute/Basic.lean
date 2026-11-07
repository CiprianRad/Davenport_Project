/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

/-!
# Codes, sets and the enumeration (computation library for Lemma 5.3)

This library has no Mathlib dependency and is compiled to native code (`precompileModules`), so that
`native_decide` evaluates the finite input of Lemma 5.3 at native speed. Its soundness is proved in
`DavenportProject.Bases.CubeFour`.
-/

@[expose] public section

namespace DavenportCompute

/-!
## Codes for `C_4^3`, and sets of codes

* The element `(x₀, x₁, x₂)` of `(ZMod 4)^3` has the code `x₀ + 4 x₁ + 16 x₂ < 64`; `add4` and
  `neg4` are addition and negation on codes.
* `P1 a`: some coordinate of `a` is odd (the element has order four). `P2 a`: the coordinate
  `x₁` or `x₂` is odd. `P3 a`: the coordinate `x₂` is odd. The codes `1`, `4` and `16` of the
  standard basis are the least codes with these properties.
* A set of codes is a `UInt64` bit mask. `shiftSet S x` is the translate `S + x`.
* For a list `p` of codes, `R1 p`, `R2 p` and `R3 p` are the sets of sums of one, two and three
  entries of `p` at distinct positions (sums over sublists of length `1`, `2`, `3`).
-/

/-- The code of the sum of the elements with codes `a` and `b`. -/
def add4 (a b : Nat) : Nat :=
  (a % 4 + b % 4) % 4 + 4 * ((a / 4 % 4 + b / 4 % 4) % 4) + 16 * ((a / 16 % 4 + b / 16 % 4) % 4)

/-- The code of the negative of the element with code `a`. -/
def neg4 (a : Nat) : Nat :=
  (4 - a % 4) % 4 + 4 * ((4 - a / 4 % 4) % 4) + 16 * ((4 - a / 16 % 4) % 4)

/-- Some coordinate is odd. -/
def P1 (a : Nat) : Bool := a % 2 == 1 || a / 4 % 2 == 1 || a / 16 % 2 == 1

/-- The coordinate `x₁` or `x₂` is odd. -/
def P2 (a : Nat) : Bool := a / 4 % 2 == 1 || a / 16 % 2 == 1

/-- The coordinate `x₂` is odd. -/
def P3 (a : Nat) : Bool := a / 16 % 2 == 1

/-- The singleton set `{x}`. -/
def bit (x : Nat) : UInt64 := 1 <<< x.toUInt64

/-- Membership of `x` in the set `S`. -/
def mem (S : UInt64) (x : Nat) : Bool := (S >>> x.toUInt64) &&& 1 != 0

/-- `shiftAux S x n T` adds to `T` the translates `b + x` of the members `b < n` of `S`. -/
def shiftAux (S : UInt64) (x : Nat) : Nat → UInt64 → UInt64
  | 0, T => T
  | n + 1, T => shiftAux S x n (if mem S n then T ||| bit (add4 n x) else T)

/-- The translate `S + x` of a set of codes. -/
def shiftSet (S : UInt64) (x : Nat) : UInt64 := shiftAux S x 64 0

/-- The set of entries of `p`. -/
def R1 : List Nat → UInt64
  | [] => 0
  | x :: p => R1 p ||| bit x

/-- The set of sums of two entries of `p` at distinct positions. -/
def R2 : List Nat → UInt64
  | [] => 0
  | x :: p => R2 p ||| shiftSet (R1 p) x

/-- The set of sums of three entries of `p` at distinct positions. -/
def R3 : List Nat → UInt64
  | [] => 0
  | x :: p => R3 p ||| shiftSet (R2 p) x

/-- The code of the sum of a list of codes. -/
def codeSum : List Nat → Nat
  | [] => 0
  | x :: p => add4 x (codeSum p)

/-!
## The certificate checker for integral incidence identities over `C_m^3`

A sequence is a list `l` of codes
`x₀ + m x₁ + m² x₂`; an index set is a bit mask over the positions of `l`; a certificate is a
list of pairs `(mask, c_E)`. `check m t l cert` tests that every mask is a nonempty zero set,
that the coefficients sum to one, and that all moments of degree `1 ≤ |J| ≤ t` vanish
(`t ≤ 2`). Its soundness theorem is
`DavenportProject.CubeFour.hasIncidenceIdentity_of_check`.

`longZero l Z` tests that the mask `Z` is a zero set of `l` with at least fifteen positions.
-/

/-- A certificate: pairs `(mask, c_E)`; repeated masks are allowed, their coefficients add up. -/
abbrev Cert := List (Nat × Int)

/-- Digit `i` of the code `a` in base `m`. -/
def digit (m a i : Nat) : Nat := a / m ^ i % m

/-- `maskSum g l E j = ∑ g (l[k])` over the positions `k` of `l` such that bit `j + k` of `E` is
set. -/
def maskSum (g : Nat → Nat) : List Nat → Nat → Nat → Nat
  | [], _, _ => 0
  | a :: l, E, j => (if E.testBit j then g a else 0) + maskSum g l E (j + 1)

/-- The mask `E` is a nonempty zero set of the code list `l`. -/
def isZeroMask (m : Nat) (l : List Nat) (E : Nat) : Bool :=
  (List.range l.length).any (E.testBit ·) &&
    maskSum (digit m · 0) l E 0 % m == 0 &&
    maskSum (digit m · 1) l E 0 % m == 0 &&
    maskSum (digit m · 2) l E 0 % m == 0

/-- Sum of the coefficients of the certificate entries whose mask satisfies `P`. -/
def coeffSum (P : Nat → Bool) (cert : Cert) : Int :=
  ((cert.filter fun p => P p.1).map Prod.snd).sum

/-- The checker. Degrees `t ≤ 2` are supported. -/
def check (m t : Nat) (l : List Nat) (cert : Cert) : Bool :=
  let n := l.length
  decide (t ≤ 2) &&
    cert.all (fun p => isZeroMask m l p.1) &&
    coeffSum (fun _ => true) cert == 1 &&
    (decide (t < 1) || (List.range n).all fun j => coeffSum (·.testBit j) cert == 0) &&
    (decide (t < 2) || (List.range n).all fun j => (List.range' (j + 1) (n - (j + 1))).all
      fun k => coeffSum (fun E => E.testBit j && E.testBit k) cert == 0)

/-- The number of positions `i < n` whose bit is set in `Z`. -/
def popcountBelow (n Z : Nat) : Nat := (List.range n).countP (Z.testBit ·)

/-- `Z` is a zero set of `l` with at least fifteen positions. -/
def longZero (l : List Nat) (Z : Nat) : Bool :=
  isZeroMask 4 l Z && decide (15 ≤ popcountBelow l.length Z)

/-!
## The enumeration of normalized short-zero-free sequences over `C_4^3`

`gdfs leaf n lo acc r1 r2 r3` walks through all non-decreasing lists of `n` further codes
`lo ≤ x < 64` appended to `acc` (most recent first), with `r1 r2 r3 = R1 acc, R2 acc, R3 acc`,
and tests `leaf` on each completed list. A code `x` is skipped (`skip`) when
* `-x` is a sum of one, two or three earlier entries (a zero set of size at most four), or
* `x` violates a normalization guard: `P1 x` while `1` was not chosen (and `x ≠ 1`), `P2 x`
  while `4` was not chosen (and `x ≠ 4`), or `P3 x` while `16` was not chosen (and `x ≠ 16`).

`n3cond acc` is the multiplicity normalization: every entry `x` with `P1 x` occurs at most as
often as `1`, every entry with `P2 x` at most as often as `4`, and every entry with `P3 x` at
most as often as `16`.
-/

/-- Appending `x` is excluded (see the section docstring). -/
def skip (r1 r2 r3 : UInt64) (x : Nat) : Bool :=
  mem (r1 ||| r2 ||| r3) (neg4 x) ||
    (P1 x && x != 1 && !mem r1 1) || (P2 x && x != 4 && !mem r1 4) ||
    (P3 x && x != 16 && !mem r1 16)

/-- `allFrom f x n` tests `f y` for `x ≤ y < x + n`. -/
def allFrom (f : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | x, n + 1 => f x && allFrom f (x + 1) n

/-- The enumeration (see the section docstring). -/
def gdfs (leaf : List Nat → Bool) : Nat → Nat → List Nat → UInt64 → UInt64 → UInt64 → Bool
  | 0, _, acc, _, _, _ => leaf acc
  | n + 1, lo, acc, r1, r2, r3 =>
    allFrom (fun x => skip r1 r2 r3 x ||
      gdfs leaf n x (x :: acc) (r1 ||| bit x) (r2 ||| shiftSet r1 x) (r3 ||| shiftSet r2 x))
      lo (64 - lo)

/-- The multiplicity normalization (see the section docstring). -/
def n3cond (acc : List Nat) : Bool :=
  acc.all fun x => (!P1 x || decide (acc.count x ≤ acc.count 1)) &&
    (!P2 x || decide (acc.count x ≤ acc.count 4)) && (!P3 x || decide (acc.count x ≤ acc.count 16))

/-- Continue the enumeration from the prefix `acc` (most recent first) with `n` further codes. -/
def gdfsFrom (leaf : List Nat → Bool) (n : Nat) (acc : List Nat) : Bool :=
  gdfs leaf n (acc.headD 1) acc (R1 acc) (R2 acc) (R3 acc)

end DavenportCompute
