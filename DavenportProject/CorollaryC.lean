/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Invariants
public import Mathlib.GroupTheory.PGroup
import DavenportProject.TheoremB
import DavenportProject.Transfer.Olson
import DavenportProject.Transfer.TheoremA

/-!
# Corollary C

* `davenport_zmod_prod_three` (Corollary C): for `m ∈ {2, 3, 4}`, a prime `p ∤ m` and
  `a ≤ b ≤ c`, `D(C_{mp^a} ⊕ C_{mp^b} ⊕ C_{mp^c}) = m(p^a + p^b + p^c) - 2`.
* `davenport_cube_three_mul_prime_pow`, `davenport_cube_four_mul_prime_pow`: the cubes
  `C_{3p^a}^3` and `C_{4p^a}^3`.
* Numerical instances: `D(C_15^3) = 43`, `D(C_20^3) = 58`, `D(C_21^3) = 61`, `D(C_28^3) = 82`,
  `D(C_36^3) = 106`, `D(C_3 ⊕ C_15 ⊕ C_75) = 91` and `D(C_4 ⊕ C_20 ⊕ C_100) = 122`. The paper
  works out `D(C_15^3) = 43` (Introduction) and `D(C_3 ⊕ C_15 ⊕ C_75) = 91` (Section 6).

The upper bound is Theorem A for integral identities applied to Theorem B (eq. (6.1)); the lower
bound is the basis bound `D(G) ≥ D*(G)`.
-/

public section

namespace DavenportProject

open Finset Transfer

namespace CorollaryC

/-!
## The Chinese remainder splitting in Corollary C

For a prime `p ∤ m`, the Chinese remainder theorem identifies
`C_m^3 ⊕ (C_{p^a} ⊕ C_{p^b} ⊕ C_{p^c})` with `C_{mp^a} ⊕ C_{mp^b} ⊕ C_{mp^c}`.
-/

/-- For a prime `p ∤ m`, `m` is coprime to every power of `p`. -/
theorem coprime_pow_of_not_dvd {m p : ℕ} [hp : Fact p.Prime] (hpm : ¬ p ∣ m) (x : ℕ) :
    m.Coprime (p ^ x) :=
  Nat.Coprime.pow_right x ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpm).symm

/-- The Chinese remainder isomorphism `ZMod (m * p ^ x) ≃+ ZMod m × ZMod (p ^ x)` for `p ∤ m`. -/
noncomputable def crtAddEquiv {m p : ℕ} [Fact p.Prime] (hpm : ¬ p ∣ m) (x : ℕ) :
    ZMod (m * p ^ x) ≃+ ZMod m × ZMod (p ^ x) :=
  (ZMod.chineseRemainder (coprime_pow_of_not_dvd hpm x)).toAddEquiv

/-- For a prime `p ∤ m`,
`(ZMod m)^3 × (ZMod (p^a) × ZMod (p^b) × ZMod (p^c)) ≃+ ZMod (mp^a) × ZMod (mp^b) × ZMod (mp^c)`. -/
noncomputable def zmodProdThreeAddEquiv (m : ℕ) (p : ℕ) [Fact p.Prime] (hpm : ¬ p ∣ m)
    (a b c : ℕ) :
    (Fin 3 → ZMod m) × (ZMod (p ^ a) × ZMod (p ^ b) × ZMod (p ^ c)) ≃+
      ZMod (m * p ^ a) × ZMod (m * p ^ b) × ZMod (m * p ^ c) where
  toFun y := ((crtAddEquiv hpm a).symm (y.1 0, y.2.1),
    (crtAddEquiv hpm b).symm (y.1 1, y.2.2.1), (crtAddEquiv hpm c).symm (y.1 2, y.2.2.2))
  invFun z := (![(crtAddEquiv hpm a z.1).1, (crtAddEquiv hpm b z.2.1).1,
      (crtAddEquiv hpm c z.2.2).1],
    ((crtAddEquiv hpm a z.1).2, (crtAddEquiv hpm b z.2.1).2, (crtAddEquiv hpm c z.2.2).2))
  left_inv y := by
    obtain ⟨f, x, y, z⟩ := y
    ext i
    · fin_cases i <;> simp
    all_goals simp
  right_inv z := by
    obtain ⟨x, y, z⟩ := z
    simp
  map_add' y z := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ← map_add, Prod.mk_add_mk]

/-!
## The `p`-part of the group in Corollary C is a `p`-group

`H = C_{p^a} ⊕ C_{p^b} ⊕ C_{p^c}` is a finite abelian `p`-group.
-/

/-- `C_{p^a} ⊕ C_{p^b} ⊕ C_{p^c}` is a `p`-group. -/
theorem isPGroup_zmod_prod_three (p : ℕ) [Fact p.Prime] (a b c : ℕ) :
    IsPGroup p (Multiplicative (ZMod (p ^ a) × ZMod (p ^ b) × ZMod (p ^ c))) := by
  refine IsPGroup.of_card (n := a + b + c) ?_
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_zmod,
    Nat.card_zmod, Nat.card_zmod, pow_add, pow_add, mul_assoc]

/-!
## The lower bound `D(G) ≥ D*(G)`

For `G = ∏ᵢ ZMod nᵢ` the sequence with `nᵢ - 1` copies of each basis vector `eᵢ` is zero-sum
free of length `∑ᵢ (nᵢ - 1)`. If `D(G) ≤ ∑ᵢ (nᵢ - 1)`, its initial segment of length `D(G)`
would have a zero set by `davenport_eq_iff`, a contradiction. The divisibility hypotheses are
not needed for this direction (adapted from the lower bound in the proof of Olson's theorem).
-/

/-- The index type of the basis sequence: `nᵢ - 1` slots for each coordinate `i`. -/
abbrev BasisIdx {r : ℕ} (n : Fin r → ℕ) : Type := (i : Fin r) × Fin (n i - 1)

/-- The basis sequence: slot `⟨i, k⟩` carries the basis vector `eᵢ`. -/
noncomputable def basisSeq {r : ℕ} (n : Fin r → ℕ) (x : BasisIdx n) :
    (i : Fin r) → ZMod (n i) :=
  Pi.single x.1 1

theorem card_basisIdx {r : ℕ} (n : Fin r → ℕ) :
    Fintype.card (BasisIdx n) = ∑ i, (n i - 1) := by
  simp

/-- The basis sequence is zero-sum free (no hypothesis on `n` is needed). -/
theorem not_isZeroSet_basisSeq {r : ℕ} (n : Fin r → ℕ) (E : Finset (BasisIdx n)) :
    ¬ IsZeroSet (basisSeq n) E := by
  classical
  rintro ⟨⟨x, hx⟩, hsum⟩
  set i := x.1
  have hi := congrFun hsum i
  simp only [basisSeq, Finset.sum_apply, Pi.zero_apply] at hi
  have hterm : ∀ y ∈ E, (Pi.single y.1 1 : (i : Fin r) → ZMod (n i)) i =
      if i = y.1 then 1 else 0 := by
    rintro ⟨j, k⟩ -
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  rw [sum_congr rfl hterm] at hi
  rw [sum_boole, ZMod.natCast_eq_zero_iff] at hi
  have hpos : 0 < #{y ∈ E | i = y.1} := card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩
  have hle : #{y ∈ E | i = y.1} ≤ #(range (n i - 1)) := by
    refine card_le_card_of_injOn (fun y => (y.2 : ℕ)) ?_ ?_
    · intro y hy
      have hy' := (mem_filter.mp hy).2
      simp only [coe_range, Set.mem_Iio]
      have h1 := y.2.2
      have h2 : n i = n y.1 := by rw [hy']
      omega
    · intro y hy z hz hyz
      obtain ⟨yi, yk⟩ := y
      obtain ⟨zi, zk⟩ := z
      have hy' := (mem_filter.mp hy).2
      have hz' := (mem_filter.mp hz).2
      simp only at hy' hz' hyz
      subst hy' hz'
      simp [Fin.ext hyz]
  rw [card_range] at hle
  have := Nat.le_of_dvd hpos hi
  omega

/-- `D(C_{n_1} ⊕ ⋯ ⊕ C_{n_r}) ≥ 1 + ∑_i (n_i - 1)`, which is `D*(G)` when
`1 < n_1 ∣ ⋯ ∣ n_r`; the bound needs neither condition. -/
theorem one_add_sum_le_davenport {r : ℕ} (n : Fin r → ℕ) [∀ i, NeZero (n i)] :
    1 + ∑ i, (n i - 1) ≤ davenport ((i : Fin r) → ZMod (n i)) := by
  classical
  by_contra hlt
  push Not at hlt
  set D := davenport ((i : Fin r) → ZMod (n i))
  obtain ⟨hforce, -⟩ := (davenport_eq_iff ((i : Fin r) → ZMod (n i)) D).mp rfl
  let e : Fin D ↪ BasisIdx n :=
    (Fin.castLEEmb (by rw [card_basisIdx]; omega)).trans
      (Fintype.equivFinOfCardEq rfl).symm.toEmbedding
  obtain ⟨E, hne, hsum⟩ := hforce (basisSeq n ∘ e)
  exact not_isZeroSet_basisSeq n (E.map e) ⟨hne.map, by rw [sum_map]; exact hsum⟩

/-!
## The lower bound in Corollary C

The basis lower bound: for `m ∈ {2, 3, 4}`, a prime `p` and `a ≤ b ≤ c`,
`m(p^a + p^b + p^c) - 2 ≤ D(C_{mp^a} ⊕ C_{mp^b} ⊕ C_{mp^c})`.

This is the bound `one_add_sum_le_davenport` for `n = ![mp^a, mp^b, mp^c]`, transported from the
Pi carrier to the product carrier along `davenport_congr`.
-/

/-- The Pi carrier `∀ i : Fin 3, ZMod (![x, y, z] i)` is the product `ZMod x × ZMod y × ZMod z`. -/
def piFinThreeZModAddEquiv (x y z : ℕ) :
    ((i : Fin 3) → ZMod (![x, y, z] i)) ≃+ ZMod x × ZMod y × ZMod z where
  toFun f := (f 0, f 1, f 2)
  invFun w := Fin.cons (α := fun i => ZMod (![x, y, z] i)) w.1
    (Fin.cons (α := fun i => ZMod (![y, z] i)) w.2.1
      (Fin.cons (α := fun i => ZMod (![z] i)) w.2.2 finZeroElim))
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- For `m ∈ {2, 3, 4}` and a prime `p`,
`m(p^a + p^b + p^c) - 2 ≤ D(C_{mp^a} ⊕ C_{mp^b} ⊕ C_{mp^c})`. Neither the hypothesis `p ∤ m` of
Corollary C nor `a ≤ b ≤ c` is needed for this direction. -/
theorem le_davenport_zmod_prod_three (m : ℕ) [NeZero m] (hm : m = 2 ∨ m = 3 ∨ m = 4) (p : ℕ)
    [Fact p.Prime] (a b c : ℕ) :
    m * (p ^ a + p ^ b + p ^ c) - 2 ≤
      davenport (ZMod (m * p ^ a) × ZMod (m * p ^ b) × ZMod (m * p ^ c)) := by
  have hm2 : 2 ≤ m := by omega
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpow : ∀ x, 2 ≤ m * p ^ x := fun x =>
    le_mul_of_le_of_one_le hm2 (Nat.one_le_pow x p hp)
  set n : Fin 3 → ℕ := ![m * p ^ a, m * p ^ b, m * p ^ c] with hn_def
  have hn : ∀ i, 1 < n i := by
    intro i
    fin_cases i
    · exact hpow a
    · exact hpow b
    · exact hpow c
  have : ∀ i, NeZero (n i) := fun i => ⟨by have := hn i; omega⟩
  have hD := one_add_sum_le_davenport n
  rw [davenport_congr (piFinThreeZModAddEquiv _ _ _)] at hD
  have hsum : ∑ i, (n i - 1) = (m * p ^ a - 1) + (m * p ^ b - 1) + (m * p ^ c - 1) := by
    rw [Fin.sum_univ_three]
    rfl
  have ha := hpow a
  have hb := hpow b
  have hc := hpow c
  rw [mul_add, mul_add]
  omega

/-!
## Eq. (6.1) and Corollary C

For `m ∈ {2, 3, 4}`, a prime `p` and a finite abelian `p`-group `H`,
`D(C_m^3 ⊕ H) ≤ m(D(H) - 1) + 3m - 2` (eq. (6.1), `davenport_cube_prod_le`): this is Theorem A for
integral identities with `Q = C_m^3` and `L t = m(t + 3) - 2`, whose hypothesis is Theorem B.

Corollary C (`davenport_zmod_prod_three`):
* upper bound: by the Chinese remainder theorem (`zmodProdThreeAddEquiv`),
  `C_{mp^a} ⊕ C_{mp^b} ⊕ C_{mp^c} ≃ C_m^3 ⊕ H` with `H = C_{p^a} ⊕ C_{p^b} ⊕ C_{p^c}` a `p`-group,
  and eq. (6.1) with Olson's theorem `D(H) = 1 + (p^a - 1) + (p^b - 1) + (p^c - 1)` gives
  `D ≤ m(p^a + p^b + p^c) - 2`;
* lower bound: `le_davenport_zmod_prod_three`.

The cases `a = b = c` with `m = 3` and `m = 4` and the numerical instances follow.
-/

/-- Eq. (6.1): for `m ∈ {2,3,4}`, every prime `p` and every finite abelian `p`-group `H`,
`D(C_m^3 ⊕ H) ≤ m(D(H) - 1) + 3m - 2`. -/
theorem davenport_cube_prod_le (m : ℕ) [NeZero m] (hm : m = 2 ∨ m = 3 ∨ m = 4) (p : ℕ)
    [Fact p.Prime] (H : Type*) [AddCommGroup H] [Finite H]
    (hH : IsPGroup p (Multiplicative H)) :
    davenport ((Fin 3 → ZMod m) × H) ≤ m * (davenport H - 1) + 3 * m - 2 := by
  have h := davenport_prod_le_of_hasIncidenceIdentity_int (Fin 3 → ZMod m)
    (fun t => m * (t + 3) - 2) (fun t u => hasIncidenceIdentity_cube m hm t u) p H hH
  have hL : m * (davenport H - 1 + 3) - 2 = m * (davenport H - 1) + 3 * m - 2 := by
    rw [mul_add, mul_comm m 3]
  exact h.trans_eq hL

/-- The Pi carrier `∀ i : Fin 3, ZMod (p ^ ![a, b, c] i)` of Olson's theorem is the product
`ZMod (p ^ a) × ZMod (p ^ b) × ZMod (p ^ c)`. -/
def piFinThreeZModPowAddEquiv (p a b c : ℕ) :
    ((i : Fin 3) → ZMod (p ^ ![a, b, c] i)) ≃+ ZMod (p ^ a) × ZMod (p ^ b) × ZMod (p ^ c) where
  toFun f := (f 0, f 1, f 2)
  invFun w := Fin.cons (α := fun i => ZMod (p ^ ![a, b, c] i)) w.1
    (Fin.cons (α := fun i => ZMod (p ^ ![b, c] i)) w.2.1
      (Fin.cons (α := fun i => ZMod (p ^ ![c] i)) w.2.2 finZeroElim))
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Olson's theorem for three factors:
`D(C_{p^a} ⊕ C_{p^b} ⊕ C_{p^c}) = 1 + (p^a - 1) + (p^b - 1) + (p^c - 1)`. -/
theorem davenport_zmod_pow_prod_three (p : ℕ) [Fact p.Prime] (a b c : ℕ) :
    davenport (ZMod (p ^ a) × ZMod (p ^ b) × ZMod (p ^ c)) =
      1 + ((p ^ a - 1) + (p ^ b - 1) + (p ^ c - 1)) := by
  rw [← davenport_congr (piFinThreeZModPowAddEquiv p a b c),
    davenport_pi_zmod_prime_pow p ![a, b, c], Fin.sum_univ_three]
  rfl

/-- The cube `C_n^3 = Fin 3 → ZMod n` is the product `ZMod n × ZMod n × ZMod n`. -/
def finThreeZModAddEquiv (n : ℕ) : (Fin 3 → ZMod n) ≃+ ZMod n × ZMod n × ZMod n where
  toFun f := (f 0, f 1, f 2)
  invFun w := ![w.1, w.2.1, w.2.2]
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end CorollaryC

-- The proof does not use the paper's normalization `a ≤ b ≤ c`, which the statement keeps.
set_option linter.unusedVariables false in
open CorollaryC in
/-- **Corollary C**, eq. (1.4): for `m ∈ {2,3,4}`, a prime `p ∤ m` and
`0 ≤ a ≤ b ≤ c`, `D(C_{mp^a} ⊕ C_{mp^b} ⊕ C_{mp^c}) = m(p^a + p^b + p^c) - 2`. -/
theorem davenport_zmod_prod_three (m : ℕ) [NeZero m] (hm : m = 2 ∨ m = 3 ∨ m = 4) (p : ℕ)
    [Fact p.Prime] (hpm : ¬ p ∣ m) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    davenport (ZMod (m * p ^ a) × ZMod (m * p ^ b) × ZMod (m * p ^ c)) =
      m * (p ^ a + p ^ b + p ^ c) - 2 := by
  refine le_antisymm ?_ (le_davenport_zmod_prod_three m hm p a b c)
  rw [← davenport_congr (zmodProdThreeAddEquiv m p hpm a b c)]
  refine (davenport_cube_prod_le m hm p _ (isPGroup_zmod_prod_three p a b c)).trans_eq ?_
  rw [davenport_zmod_pow_prod_three]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨A, hA⟩ : ∃ A, p ^ a = A + 1 := ⟨p ^ a - 1, by have := Nat.one_le_pow a p hp; omega⟩
  obtain ⟨B, hB⟩ : ∃ B, p ^ b = B + 1 := ⟨p ^ b - 1, by have := Nat.one_le_pow b p hp; omega⟩
  obtain ⟨C, hC⟩ : ∃ C, p ^ c = C + 1 := ⟨p ^ c - 1, by have := Nat.one_le_pow c p hp; omega⟩
  rw [hA, hB, hC, Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.add_sub_cancel,
    Nat.add_sub_cancel_left]
  congr 1
  ring

/-- Corollary C with `a = b = c`: for `m ∈ {2,3,4}` and a prime `p ∤ m`,
`D(C_{mp^a}^3) = 3m p^a - 2`. -/
theorem CorollaryC.davenport_cube_mul_prime_pow (m : ℕ) [NeZero m]
    (hm : m = 2 ∨ m = 3 ∨ m = 4) (p : ℕ) [Fact p.Prime] (hpm : ¬ p ∣ m) (a : ℕ) :
    davenport (Fin 3 → ZMod (m * p ^ a)) = 3 * m * p ^ a - 2 := by
  rw [davenport_congr (finThreeZModAddEquiv _),
    davenport_zmod_prod_three m hm p hpm a a a le_rfl le_rfl]
  congr 1
  ring

/-- **Corollary C** for `m = 3`: `D(C_{3p^a}^3) = 9p^a - 2` for a prime `p ≠ 3`. -/
theorem davenport_cube_three_mul_prime_pow (p : ℕ) [Fact p.Prime] (hp : p ≠ 3) (a : ℕ) :
    davenport (Fin 3 → ZMod (3 * p ^ a)) = 9 * p ^ a - 2 := by
  have hpm : ¬ p ∣ 3 := fun h =>
    hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).1 h)
  rw [CorollaryC.davenport_cube_mul_prime_pow 3 (by norm_num) p hpm a]

/-- **Corollary C** for `m = 4`: `D(C_{4p^a}^3) = 12p^a - 2` for an odd prime `p`. -/
theorem davenport_cube_four_mul_prime_pow (p : ℕ) [Fact p.Prime] (hp : Odd p) (a : ℕ) :
    davenport (Fin 3 → ZMod (4 * p ^ a)) = 12 * p ^ a - 2 := by
  have hpm : ¬ p ∣ 4 := fun h => by
    have h2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow (n := 2) (by norm_num at h ⊢; exact h)
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h2
    subst this
    exact (Nat.not_even_iff_odd.2 hp) even_two
  rw [CorollaryC.davenport_cube_mul_prime_pow 4 (by norm_num) p hpm a]

/-- Numerical instance: `D(C_{15}^3) = 43`. -/
theorem davenport_cube_fifteen : davenport (Fin 3 → ZMod 15) = 43 :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  davenport_cube_three_mul_prime_pow 5 (by norm_num) 1

/-- Numerical instance: `D(C_{20}^3) = 58`. -/
theorem davenport_cube_twenty : davenport (Fin 3 → ZMod 20) = 58 :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  davenport_cube_four_mul_prime_pow 5 (by decide) 1

/-- Numerical instance: `D(C_{21}^3) = 61`. -/
theorem davenport_cube_twentyOne : davenport (Fin 3 → ZMod 21) = 61 :=
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  davenport_cube_three_mul_prime_pow 7 (by norm_num) 1

/-- Numerical instance: `D(C_{28}^3) = 82`. -/
theorem davenport_cube_twentyEight : davenport (Fin 3 → ZMod 28) = 82 :=
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  davenport_cube_four_mul_prime_pow 7 (by decide) 1

/-- Numerical instance: `D(C_{36}^3) = 106`. -/
theorem davenport_cube_thirtySix : davenport (Fin 3 → ZMod 36) = 106 :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  davenport_cube_four_mul_prime_pow 3 (by decide) 2

/-- Numerical instance: `D(C_3 ⊕ C_{15} ⊕ C_{75}) = 91`. -/
theorem davenport_zmod_three_fifteen_seventyFive :
    davenport (ZMod 3 × ZMod 15 × ZMod 75) = 91 :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  davenport_zmod_prod_three 3 (by decide) 5 (by norm_num) 0 1 2 (by norm_num) (by norm_num)

/-- Numerical instance: `D(C_4 ⊕ C_{20} ⊕ C_{100}) = 122`. -/
theorem davenport_zmod_four_twenty_hundred :
    davenport (ZMod 4 × ZMod 20 × ZMod 100) = 122 :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  davenport_zmod_prod_three 4 (by decide) 5 (by norm_num) 0 1 2 (by norm_num) (by norm_num)

end DavenportProject
