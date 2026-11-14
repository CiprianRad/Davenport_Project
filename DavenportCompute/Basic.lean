/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

/-!
# Codes and the certificate checker (computation library for Lemma 5.3)

Code arithmetic for `C_4^3`, the certificate checker for integral incidence identities and the
multiplicity normalization. This library has no Mathlib dependency; the enumeration of Lemma 5.3
is in `DavenportCompute.Search`, and the soundness of both in `DavenportProject.Bases.CubeFour`.
-/

@[expose] public section

namespace DavenportCompute

/-!
## Codes for `C_4^3`

* The element `(x₀, x₁, x₂)` of `(ZMod 4)^3` has the code `x₀ + 4 x₁ + 16 x₂ < 64`; `add4` and
  `neg4` are addition and negation on codes, and `codeSum` is the code of the sum of a list.
* `P1 a`: some coordinate of `a` is odd (the element has order four). `P2 a`: the coordinate
  `x₁` or `x₂` is odd. `P3 a`: the coordinate `x₂` is odd. The codes `1`, `4` and `16` of the
  standard basis are the least codes with these properties.
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

/-!
## The multiplicity normalization

`n3cond acc`: every entry `x` with `P1 x` occurs at most as often as `1`, every entry with `P2 x`
at most as often as `4`, and every entry with `P3 x` at most as often as `16`.
-/

/-- The multiplicity normalization (see the section docstring). -/
def n3cond (acc : List Nat) : Bool :=
  acc.all fun x => (!P1 x || decide (acc.count x ≤ acc.count 1)) &&
    (!P2 x || decide (acc.count x ≤ acc.count 4)) && (!P3 x || decide (acc.count x ≤ acc.count 16))

end DavenportCompute
