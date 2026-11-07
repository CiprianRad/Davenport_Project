/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportCompute.Basic
public import DavenportCompute.Data
public import Std.Data.HashMap

/-!
# Certificate search and leaf tests for Lemma 5.3

The search (`oracle14`, `oracleLong`, `oracle18`) is untrusted: its answers are always re-checked by
`check` or `longZero`. The leaf tests `leaf14` and `leaf18` are what the native checks evaluate.
-/

@[expose] public section

namespace DavenportCompute

/-!
## Untrusted certificate search

The soundness of `check` and `longZero` is proved, so a wrong answer of the search can only make
the computation fail.

* `findSmall l σ`: a mask of at most three positions whose entries sum to `σ`. With `σ` the
  sum of all entries, its complement is a zero set of at least `n - 3` positions.
* `splitZero l W`: a nonempty proper zero subset of the zero set `W` (it exists once `W` has
  more than ten positions, since `D(C_4^3) = 10`).
* `findPair l`: two disjoint zero sets.
* `transport table l`: for a hard case, a linear map sending three support entries to the
  standard basis whose sorted image is a stored orbit representative; the representative's
  certificate is moved back along the sorting permutation.
-/

/-- The sums of all sub-masks of the positions of `l` (index = mask). -/
def subsetSums (l : Array Nat) : Array Nat := Id.run do
  let mut s : Array Nat := #[0]
  for x in l do
    s := s ++ s.map (add4 · x)
  return s

/-- A mask of at most three positions of `l` whose entries sum to `σ`. -/
def findSmall (l : Array Nat) (σ : Nat) : Option Nat := Id.run do
  let n := l.size
  if σ == 0 then return some 0
  for i in [0:n] do
    if l[i]! == σ then return some (1 <<< i)
    for j in [i+1:n] do
      let a := add4 l[i]! l[j]!
      if a == σ then return some ((1 <<< i) ||| (1 <<< j))
      for k in [j+1:n] do
        if add4 a l[k]! == σ then return some ((1 <<< i) ||| (1 <<< j) ||| (1 <<< k))
  return none

/-- The positions `i < n` whose bit is set in `W`. -/
def positions (n W : Nat) : Array Nat := (Array.range n).filter (W.testBit ·)

/-- The mask of the positions `pos[i]` for the bits `i` of `m`. -/
def maskOf (pos : Array Nat) (m : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:pos.size] do
    if m.testBit i then r := r ||| (1 <<< pos[i]!)
  return r

/-- A nonempty zero subset of the first ten positions of `W`. -/
def splitZero (l : Array Nat) (W : Nat) : Option Nat :=
  let ps := (positions l.size W).extract 0 10
  let sums := subsetSums (ps.map (l[·]!))
  match (List.range sums.size).find? (fun m => m != 0 && sums[m]! == 0) with
  | some m => some (maskOf ps m)
  | none => none

/-- Two disjoint zero sets of `l`. -/
def findPair (l : Array Nat) : Option (Nat × Nat) := Id.run do
  let sums := subsetSums l
  let zs := (Array.range sums.size).filter (fun m => m != 0 && sums[m]! == 0)
  for i in [0:zs.size] do
    for j in [i+1:zs.size] do
      if zs[i]! &&& zs[j]! == 0 then return some (zs[i]!, zs[j]!)
  return none

/-- Coordinate `i` of a code. -/
def coord (a i : Nat) : Nat := a / 4 ^ i % 4

/-- The code of `(x, y, z)` reduced mod 4. -/
def enc3 (x y z : Nat) : Nat := x % 4 + 4 * (y % 4) + 16 * (z % 4)

/-- `v ↦ v * M` for a matrix `M` over `ZMod 4`, stored row-major. -/
def applyMat (M : Array Nat) (v : Nat) : Nat :=
  let a := coord v 0; let b := coord v 1; let c := coord v 2
  enc3 (a * M[0]! + b * M[3]! + c * M[6]!) (a * M[1]! + b * M[4]! + c * M[7]!)
    (a * M[2]! + b * M[5]! + c * M[8]!)

/-- The inverse over `ZMod 4` of the matrix with rows `r₀, r₁, r₂`, if its determinant is odd. -/
def invMat (r0 r1 r2 : Nat) : Option (Array Nat) :=
  let m : Nat → Nat → Int := fun i j => (coord ([r0, r1, r2].getD i 0) j : Int)
  let d := m 0 0 * (m 1 1 * m 2 2 - m 1 2 * m 2 1) - m 0 1 * (m 1 0 * m 2 2 - m 1 2 * m 2 0) +
    m 0 2 * (m 1 0 * m 2 1 - m 1 1 * m 2 0)
  let dm := d % 4
  if dm % 2 == 0 then none else
  -- `dm⁻¹ = dm` for the units `1, 3` of `ZMod 4`
  let adj : List Int := [m 1 1 * m 2 2 - m 1 2 * m 2 1, -(m 0 1 * m 2 2 - m 0 2 * m 2 1),
    m 0 1 * m 1 2 - m 0 2 * m 1 1, -(m 1 0 * m 2 2 - m 1 2 * m 2 0), m 0 0 * m 2 2 - m 0 2 * m 2 0,
    -(m 0 0 * m 1 2 - m 0 2 * m 1 0), m 1 0 * m 2 1 - m 1 1 * m 2 0,
    -(m 0 0 * m 2 1 - m 0 1 * m 2 0), m 0 0 * m 1 1 - m 0 1 * m 1 0]
  some (adj.map fun a => ((a * dm) % 4).toNat).toArray

/-- Move a certificate over the positions of a representative to the positions of `l`:
position `j` of the representative is position `perm[j]` of `l`. -/
def moveCert (perm : Array Nat) (cert : Cert) : Cert :=
  cert.map fun (E, c) => (maskOf perm E, c)

/-- Find a stored representative in the orbit of `l` and move its certificate to `l`. -/
def transport (table : Std.HashMap (List Nat) Cert) (l : Array Nat) : Option Cert := Id.run do
  let sup := l.toList.eraseDups
  for b0 in sup do
    for b1 in sup do
      if b1 == b0 then continue
      for b2 in sup do
        if b2 == b0 || b2 == b1 then continue
        match invMat b0 b1 b2 with
        | none => continue
        | some M =>
          let img := (l.toList.map (applyMat M)).zipIdx.mergeSort (fun p q => p.1 ≤ q.1)
          match table.get? (img.map (·.1)) with
          | some cert => return some (moveCert (img.map (·.2)).toArray cert)
          | none => continue
  return none

/-- Parse a signed decimal integer. -/
def parseInt (s : String) : Int :=
  if s.startsWith "-" then -((s.drop 1).toString.toNat! : Int) else (s.toNat! : Int)

/-- Read `m₁ k₁ m₂ k₂ …` as a certificate. -/
def parsePairs : List String → Cert
  | m :: k :: rest => (m.toNat!, parseInt k) :: parsePairs rest
  | _ => []

/-- Parse a data line `c₀ … c_{n-1} | m₁ k₁ m₂ k₂ …`. -/
def parseLine (line : String) : Option (List Nat × Cert) :=
  match line.splitOn "|" with
  | [a, b] =>
    some (((a.splitOn " ").filter (· ≠ "")).map String.toNat!,
      parsePairs ((b.splitOn " ").filter (· ≠ "")))
  | _ => none

/-- Parse a table of representatives with their certificates. -/
def parseTable (s : String) : Std.HashMap (List Nat) Cert :=
  (s.splitOn "\n").foldl (fun t line =>
    match parseLine line with
    | some (k, c) => t.insert k c
    | none => t) {}

/-!
## Leaf tests and the split of the enumeration into chunks

A leaf is a completed list `acc` of codes, most recent first, so its sequence is `acc.reverse`.
* `leaf14 acc`: if `acc` is normalized by multiplicities (`n3cond`), the oracle's certificate is a
  valid integral `𝓘_1`-identity of `acc.reverse` (`check 4 1`).
* `leaf18 acc`: if `n3cond acc`, then either the oracle's mask is a zero set with at least fifteen
  positions (`longZero`), or its certificate is a valid integral `𝓘_2`-identity (`check 4 2`).

`prefixes d` lists the prefixes of depth `d` reached by `gdfs`; `chunk k i P` is the part of `P`
whose `mix` value is `i` modulo `k`. These only organize the computation into independent
`native_decide` checks.
-/

/-- The hard fourteen-term representatives. -/
def table14 : Std.HashMap (List Nat) Cert := parseTable data14

/-- The hard eighteen-term representatives. -/
def table18 : Std.HashMap (List Nat) Cert := parseTable data18

/-- An `𝓘_1`-certificate for the leaf `acc` (untrusted). -/
def oracle14 (acc : List Nat) : Cert :=
  let l := acc.reverse.toArray
  let full := 2 ^ l.size - 1
  let viaLong : Option Cert := match findSmall l (l.foldl add4 0) with
    | some R =>
      let W := full - R
      match splitZero l W with
      | some E => if E != W then some [(E, 1), (W - E, 1), (W, -1)] else none
      | none => none
    | none => none
  match viaLong with
  | some c => c
  | none =>
    match findPair l with
    | some (E, F) => [(E, 1), (F, 1), (E ||| F, -1)]
    | none => (transport table14 l).getD []

/-- A long zero set of the leaf `acc` (untrusted; `0` if none is found). -/
def oracleLong (acc : List Nat) : Nat :=
  let l := acc.reverse.toArray
  match findSmall l (l.foldl add4 0) with
  | some R => 2 ^ l.size - 1 - R
  | none => 0

/-- An `𝓘_2`-certificate for the leaf `acc` (untrusted). -/
def oracle18 (acc : List Nat) : Cert := (transport table18 acc.reverse.toArray).getD []

/-- The leaf test for Lemma 5.3(1). -/
def leaf14 (acc : List Nat) : Bool := !n3cond acc || check 4 1 acc.reverse (oracle14 acc)

/-- The leaf test for Lemma 5.3(2). -/
def leaf18 (acc : List Nat) : Bool :=
  !n3cond acc || longZero acc.reverse (oracleLong acc) || check 4 2 acc.reverse (oracle18 acc)

/-- The prefixes of depth `n` reached by `gdfs`, from `lo` and the prefix `acc`. -/
def collectAux : Nat → Nat → List Nat → UInt64 → UInt64 → UInt64 → List (List Nat)
  | 0, _, acc, _, _, _ => [acc]
  | n + 1, lo, acc, r1, r2, r3 => (List.range' lo (64 - lo)).flatMap fun x =>
    if skip r1 r2 r3 x then [] else
      collectAux n x (x :: acc) (r1 ||| bit x) (r2 ||| shiftSet r1 x) (r3 ||| shiftSet r2 x)

/-- The prefixes of depth `d` reached by `gdfs` from the empty prefix. -/
def prefixes (d : Nat) : List (List Nat) := collectAux d 1 [] 0 0 0

/-- A hash of a prefix, used to spread prefixes over chunks. -/
def mix (p : List Nat) : Nat := p.foldl (fun a x => a * 131 + x + 7) 0

/-- The prefixes of `P` assigned to chunk `i` of `k`. -/
def chunk (k i : Nat) (P : List (List Nat)) : List (List Nat) := P.filter fun p => mix p % k == i

end DavenportCompute
