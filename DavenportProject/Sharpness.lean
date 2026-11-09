/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Invariants
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Proposition 4.1: sharpness

`le_kappa_cube`: for `m ≥ 2`, `t ≥ 0` and a field `K` whose characteristic is zero or does not
divide `m`, `m(t + 3) - 2 ≤ κ_t(C_m^3; K)`. The sequence `e₁^{m-1} e₂^{m-1} e₃^{m(t+1)-1}` of
length `m(t + 3) - 3` has a separator of degree at most `t`, built from elementary symmetric
polynomials; its existence uses the binomial determinant `det (binom(mk, j)) = m^{t(t+1)/2}`.
-/
public section

namespace DavenportProject

open Finset MvPolynomial Matrix

namespace Sharpness

/-!
## The binomial determinant `det (binom(mk, j)) = m^{t(t+1)/2}`

Proof: scaling column `j` by `j!` turns
`binom(mk, j)` into the descending Pochhammer polynomial of degree `j` (monic) evaluated at
`mk`, so the determinant becomes the Vandermonde determinant of `0, m, …, mt`, which is
`m^{t(t+1)/2}` times the superfactorial `sf t = ∏_{j ≤ t} j!`.

The paper computes the same determinant by an integer triangular factorization of the matrix.
-/

open Nat in
/-- `∏_{j ≤ t} j! = sf t`. -/
private theorem prod_factorial_fin_eq_superFactorial (t : ℕ) :
    ∏ j : Fin (t + 1), ((j : ℕ)! : ℤ) = (t.superFactorial : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Nat.superFactorial_succ]
    push_cast
    ring

open Nat in
/-- `det (binom(mk, j))_{0 ≤ k, j ≤ t} = m^{t(t+1)/2}` over `ℤ`. -/
theorem det_choose_mul (m t : ℕ) :
    (Matrix.of fun k j : Fin (t + 1) => ((Nat.choose (m * (k : ℕ)) (j : ℕ) : ℕ) : ℤ)).det =
      (m : ℤ) ^ (t * (t + 1) / 2) := by
  set B := Matrix.of fun k j : Fin (t + 1) => ((Nat.choose (m * (k : ℕ)) (j : ℕ) : ℕ) : ℤ)
  have hA : Matrix.of (fun k j : Fin (t + 1) =>
      (descPochhammer ℤ (j : ℕ)).eval ((m * (k : ℕ) : ℕ) : ℤ)) =
      B * Matrix.diagonal (fun j : Fin (t + 1) => (((j : ℕ)! : ℕ) : ℤ)) := by
    ext k j
    rw [Matrix.of_apply, Matrix.mul_diagonal, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose]
    simp only [B, Matrix.of_apply]
    push_cast
    ring
  have hV := det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun k : Fin (t + 1) => ((m * (k : ℕ) : ℕ) : ℤ)) (fun j => descPochhammer ℤ (j : ℕ))
    (fun j => descPochhammer_natDegree ℤ _) (fun j => monic_descPochhammer ℤ _)
  rw [hA, det_mul, det_diagonal] at hV
  have hW : vandermonde (fun k : Fin (t + 1) => ((m * (k : ℕ) : ℕ) : ℤ)) =
      vandermonde (fun k : Fin (t + 1) => ((k : ℕ) : ℤ)) *
        Matrix.diagonal (fun j : Fin (t + 1) => (m : ℤ) ^ (j : ℕ)) := by
    ext k j
    rw [Matrix.mul_diagonal, vandermonde_apply, vandermonde_apply]
    push_cast
    ring
  rw [hW, det_mul, det_diagonal, det_vandermonde_id_eq_superFactorial,
    Finset.prod_pow_eq_pow_sum] at hV
  have hsum : ∑ j : Fin (t + 1), (j : ℕ) = t * (t + 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => j) (t + 1), Finset.sum_range_id, mul_comm]
    rfl
  have hprod := prod_factorial_fin_eq_superFactorial t
  rw [← hprod, hsum] at hV
  have hsf : ∏ j : Fin (t + 1), (((j : ℕ)! : ℕ) : ℤ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast Nat.factorial_ne_zero _
  exact mul_right_cancel₀ hsf (by rw [← hV]; ring)

/-!
## Elementary symmetric polynomials in a block of variables

For a finite set `T` of variables, `esymmOn K T j = ∑_{S ⊆ T, |S| = j} ∏_{i ∈ S} X_i` is the
elementary symmetric polynomial of degree `j` in the variables of `T`.
On the incidence vector of a subset `E ⊆ T` it takes the value `binom(|E|, j)`.
-/

section EsymmOn

variable {ι : Type*} (K : Type*) [Field K]

/-- The elementary symmetric polynomial of degree `j` in the variables indexed by `T`. -/
noncomputable def esymmOn (T : Finset ι) (j : ℕ) : MvPolynomial ι K :=
  ∑ S ∈ T.powersetCard j, ∏ i ∈ S, X i

theorem totalDegree_esymmOn_le (T : Finset ι) (j : ℕ) : (esymmOn K T j).totalDegree ≤ j := by
  refine totalDegree_finsetSum_le fun S hS => ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  simp only [totalDegree_X, sum_const, smul_eq_mul, mul_one]
  exact (mem_powersetCard.mp hS).2.le

theorem eval_esymmOn {T E : Finset ι} (hE : E ⊆ T) (j : ℕ) :
    eval ((E : Set ι).indicator 1) (esymmOn K T j) = ((E.card.choose j : ℕ) : K) := by
  classical
  have hprod : ∀ S : Finset ι, ∏ i ∈ S, (E : Set ι).indicator (1 : ι → K) i =
      if S ⊆ E then 1 else 0 := by
    intro S
    simp only [Set.indicator_apply, Finset.mem_coe, Pi.one_apply]
    rw [Finset.prod_boole]
    rfl
  simp only [esymmOn, map_sum, map_prod, eval_X, hprod]
  rw [Finset.sum_boole]
  have hfilt : (T.powersetCard j).filter (· ⊆ E) = E.powersetCard j := by
    ext S
    simp only [mem_filter, mem_powersetCard]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hE, h.2⟩, h.1⟩⟩
  rw [hfilt, card_powersetCard]

end EsymmOn

/-!
## The extremal sequence `e₁^{m-1} e₂^{m-1} e₃^{m(t+1)-1}` and its zero sets

Positions `i < m - 1` carry `e₁`, positions `m - 1 ≤ i < 2(m - 1)` carry
`e₂`, and the remaining positions carry `e₃`. Every zero set consists of third-axis positions
only, and its size is a multiple `mk` of `m` with `k` below the number of third-axis positions
divided by `m`.
-/

/-- The axis carried by position `i`. -/
def axisOf (m i : ℕ) : Fin 3 :=
  if i < m - 1 then 0 else if i < 2 * (m - 1) then 1 else 2

/-- The sequence `e₁^{m-1} e₂^{m-1} e₃^{n - 2(m-1)}` of length `n` over `(ℤ/m)^3`. -/
noncomputable def cubeSeq (m n : ℕ) (i : Fin n) : Fin 3 → ZMod m :=
  Pi.single (axisOf m i) 1

/-- The third-axis positions. -/
def thirdAxis (m n : ℕ) : Finset (Fin n) :=
  univ.filter fun i => axisOf m i = 2

theorem sum_cubeSeq_apply (m n : ℕ) (E : Finset (Fin n)) (c : Fin 3) :
    (∑ i ∈ E, cubeSeq m n i) c = ((E.filter fun i : Fin n => c = axisOf m i).card : ZMod m) := by
  rw [Finset.sum_apply]
  simp only [cubeSeq, Pi.single_apply]
  rw [Finset.sum_boole]

/-- A subset of positions on one axis whose size is divisible by `m`, and which lies in an
interval of fewer than `m · k` positions, has size `m · j` with `j < k`. -/
private theorem card_eq_of_dvd {m n a b k : ℕ} (s : Finset (Fin n))
    (hs : ∀ i ∈ s, a ≤ (i : ℕ) ∧ (i : ℕ) < b) (hab : b - a < m * k)
    (hdvd : m ∣ s.card) : ∃ j < k, s.card = m * j := by
  obtain ⟨j, hj⟩ := hdvd
  refine ⟨j, ?_, hj⟩
  have hle : s.card ≤ (Ico a b).card :=
    card_le_card_of_injOn (fun i : Fin n => (i : ℕ))
      (fun i hi => by simpa using hs i hi) (fun x _ y _ h => Fin.ext h)
  rw [Nat.card_Ico] at hle
  by_contra h
  have : m * k ≤ m * j := Nat.mul_le_mul_left m (not_lt.mp h)
  omega

/-- Every zero set of `e₁^{m-1} e₂^{m-1} e₃^{m(t+1)-1}` consists of third-axis
positions and has size `mk` with `1 ≤ k ≤ t`. -/
theorem isZeroSet_cubeSeq {m t n : ℕ} (hm : 1 ≤ m) (hn : n = 2 * (m - 1) + (m * (t + 1) - 1))
    {E : Finset (Fin n)} (hE : IsZeroSet (cubeSeq m n) E) :
    E ⊆ thirdAxis m n ∧ ∃ k, 1 ≤ k ∧ k ≤ t ∧ E.card = m * k := by
  obtain ⟨hne, hsum⟩ := hE
  have hdvd : ∀ c : Fin 3, m ∣ (E.filter fun i : Fin n => c = axisOf m i).card := fun c => by
    rw [← ZMod.natCast_eq_zero_iff, ← sum_cubeSeq_apply, hsum, Pi.zero_apply]
  have hax : ∀ i : Fin n, axisOf m i = 0 ∧ (i : ℕ) < m - 1 ∨
      axisOf m i = 1 ∧ m - 1 ≤ (i : ℕ) ∧ (i : ℕ) < 2 * (m - 1) ∨
      axisOf m i = 2 ∧ 2 * (m - 1) ≤ (i : ℕ) ∧ (i : ℕ) < n := fun i => by
    unfold axisOf
    have := i.isLt
    split_ifs <;> simp <;> omega
  have hempty : ∀ c : Fin 3, c ≠ 2 → (E.filter fun i : Fin n => c = axisOf m i) = ∅ := by
    intro c hc
    rw [← Finset.card_eq_zero]
    have hc' : c = 0 ∨ c = 1 := by omega
    rcases hc' with rfl | rfl
    · obtain ⟨j, hj, hcard⟩ := card_eq_of_dvd (m := m) (n := n) (a := 0) (b := m - 1) (k := 1) _
        (fun i hi => by
          have := (mem_filter.mp hi).2
          rcases hax i with h | h | h
          · exact ⟨Nat.zero_le _, h.2⟩
          · exact absurd (this.trans h.1) (by decide)
          · exact absurd (this.trans h.1) (by decide)) (by omega) (hdvd 0)
      rw [hcard, Nat.lt_one_iff.mp hj, mul_zero]
    · obtain ⟨j, hj, hcard⟩ := card_eq_of_dvd (m := m) (n := n)
        (a := m - 1) (b := 2 * (m - 1)) (k := 1) _
        (fun i hi => by
          have := (mem_filter.mp hi).2
          rcases hax i with h | h | h
          · exact absurd (this.trans h.1) (by decide)
          · exact h.2
          · exact absurd (this.trans h.1) (by decide)) (by omega) (hdvd 1)
      rw [hcard, Nat.lt_one_iff.mp hj, mul_zero]
  have hsub : E ⊆ thirdAxis m n := by
    intro i hi
    simp only [thirdAxis, mem_filter, mem_univ, true_and]
    by_contra h
    have := hempty (axisOf m i) h
    rw [Finset.eq_empty_iff_forall_notMem] at this
    exact this i (mem_filter.mpr ⟨hi, rfl⟩)
  have hfilt : (E.filter fun i : Fin n => (2 : Fin 3) = axisOf m i) = E := by
    refine Finset.filter_true_of_mem fun i hi => ?_
    have := hsub hi
    simp only [thirdAxis, mem_filter, mem_univ, true_and] at this
    exact this.symm
  obtain ⟨k, hk, hcard⟩ := card_eq_of_dvd (m := m) (n := n)
    (a := 2 * (m - 1)) (b := n) (k := t + 1) _
    (fun i hi => by
      have := (mem_filter.mp hi).2
      rcases hax i with h | h | h
      · exact absurd (this.trans h.1) (by decide)
      · exact absurd (this.trans h.1) (by decide)
      · exact h.2) (by
        have : 0 < m * (t + 1) := Nat.mul_pos hm (Nat.succ_pos t)
        omega) (hdvd 2)
  rw [hfilt] at hcard
  refine ⟨hsub, k, ?_, by omega, hcard⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [mul_zero, Finset.card_eq_zero] at hcard
    exact absurd hcard hne.ne_empty
  · exact hk0

/-!
## Separators pass to shorter sequences

A separator of degree `t` for a
sequence of `N` terms restricts, by setting the last `N - N'` variables to zero, to a separator
of degree `t` for the first `N'` terms.
-/

variable {G : Type*} [AddCommGroup G]

/-- Substituting polynomials of total degree at most one does not raise the total degree. -/
theorem totalDegree_bind₁_le {σ τ R : Type*} [CommSemiring R] (g : σ → MvPolynomial τ R)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (bind₁ g p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ s.support, (g i ^ s i).totalDegree
      ≤ ∑ i ∈ s.support, s i := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hg i))
    _ = s.sum fun _ e => e := rfl
    _ ≤ p.totalDegree := le_totalDegree hs

/-- The truncation map `Fin N → MvPolynomial (Fin N') K`: `X_i` for `i < N'`, else `0`. -/
noncomputable def truncVar (K : Type*) [Field K] (N' N : ℕ) (i : Fin N) :
    MvPolynomial (Fin N') K :=
  if h : (i : ℕ) < N' then X ⟨i, h⟩ else 0

theorem eval_truncVar {K : Type*} [Field K] {N' N : ℕ} (hN : N' ≤ N) (E : Finset (Fin N'))
    (i : Fin N) :
    eval ((E : Set (Fin N')).indicator 1) (truncVar K N' N i) =
      ((E.map (Fin.castLEEmb hN) : Set (Fin N)).indicator 1) i := by
  unfold truncVar
  split_ifs with h
  · rw [eval_X]
    obtain ⟨j, rfl⟩ : ∃ j : Fin N', Fin.castLEEmb hN j = i := ⟨⟨i, h⟩, Fin.ext rfl⟩
    rw [Finset.coe_map, Set.indicator_image (Fin.castLEEmb hN).injective]
    rfl
  · rw [map_zero, eq_comm, Set.indicator_of_notMem]
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, not_exists, not_and]
    intro j _ hj
    exact h (hj ▸ (by simp))

/-- a separator of degree `t` for some sequence of
`N` terms gives one for some sequence of every length `N' ≤ N`; equivalently, absence of
separators at length `N` is inherited by longer sequences. -/
theorem exists_hasSeparator_of_le (K : Type*) [Field K] {t N N' : ℕ} (hN : N' ≤ N)
    (h : ∃ u : Fin N → G, HasSeparator K u t) :
    ∃ u : Fin N' → G, HasSeparator K u t := by
  obtain ⟨u, P, hdeg, h0, hz⟩ := h
  have hev : ∀ E : Finset (Fin N'),
      eval ((E : Set (Fin N')).indicator 1) (bind₁ (truncVar K N' N) P) =
        eval ((E.map (Fin.castLEEmb hN) : Set (Fin N)).indicator 1) P := by
    intro E
    change eval₂Hom (RingHom.id K) _ (bind₁ _ P) = _
    rw [eval₂Hom_bind₁]
    exact congrArg (fun x => eval x P) (funext (eval_truncVar hN E))
  refine ⟨u ∘ Fin.castLEEmb hN, bind₁ (truncVar K N' N) P, ?_, ?_, ?_⟩
  · refine (totalDegree_bind₁_le _ (fun i => ?_) P).trans hdeg
    unfold truncVar
    split_ifs
    · rw [totalDegree_X]
    · rw [totalDegree_zero]; exact zero_le_one
  · have := hev ∅
    simp only [Finset.coe_empty, Set.indicator_empty, Finset.map_empty] at this
    exact this.trans h0
  · intro E hE
    rw [hev]
    refine hz _ ⟨hE.1.map, ?_⟩
    rw [Finset.sum_map]
    exact hE.2

/-!
## The explicit separator of Proposition 4.1

The binomial matrix `B = (binom(mk, j))_{0 ≤ k, j ≤ t}` has determinant
`m^{t(t+1)/2}`, which is nonzero in `K` when `m ≠ 0` in `K`. Hence a linear combination
`P = ∑_j c_j e_j` of the elementary symmetric polynomials in the third-axis variables can be
chosen with `P(𝟙_E) = [k = 0]` for every set `E` of `mk` third-axis positions, `0 ≤ k ≤ t`.
It has degree at most `t`, equals one at the empty set and vanishes on all zero sets.
-/

/-- `m ≠ 0` in a field of characteristic zero or of characteristic not dividing `m`. -/
theorem natCast_ne_zero_of_ringChar (m : ℕ) [NeZero m] (K : Type*) [Field K]
    (hK : ringChar K = 0 ∨ ¬ ringChar K ∣ m) : (m : K) ≠ 0 := by
  intro h
  have hdvd := (ringChar.spec K m).mp h
  rcases hK with h0 | h0
  · rw [h0, zero_dvd_iff] at hdvd
    exact NeZero.ne m hdvd
  · exact h0 hdvd

/-- The sequence `e₁^{m-1} e₂^{m-1} e₃^{m(t+1)-1}` of length `m(t+3) - 3`
has a separator of degree `t` over `K` whenever `m ≠ 0` in `K`. -/
theorem hasSeparator_cubeSeq (m : ℕ) (hm : 1 ≤ m) (t : ℕ) (K : Type*) [Field K]
    (hmK : (m : K) ≠ 0) {n : ℕ} (hn : n = 2 * (m - 1) + (m * (t + 1) - 1)) :
    HasSeparator K (cubeSeq m n) t := by
  set BK : Matrix (Fin (t + 1)) (Fin (t + 1)) K :=
    Matrix.of fun k j => ((Nat.choose (m * (k : ℕ)) (j : ℕ) : ℕ) : K) with hBK
  have hdet : BK.det ≠ 0 := by
    have h := congrArg (Int.castRingHom K) (det_choose_mul m t)
    rw [RingHom.map_det] at h
    have hmap : (Int.castRingHom K).mapMatrix
        (Matrix.of fun k j : Fin (t + 1) => ((Nat.choose (m * (k : ℕ)) (j : ℕ) : ℕ) : ℤ)) =
          BK := by
      ext k j
      simp [hBK]
    rw [hmap, map_pow, eq_intCast, Int.cast_natCast] at h
    rw [h]
    exact pow_ne_zero _ hmK
  set c : Fin (t + 1) → K := BK⁻¹ *ᵥ Pi.single 0 1 with hc_def
  have hc : BK *ᵥ c = Pi.single 0 1 := by
    rw [hc_def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  set T := thirdAxis m n
  set P : MvPolynomial (Fin n) K := ∑ j : Fin (t + 1), C (c j) * esymmOn K T j with hP
  have key : ∀ E : Finset (Fin n), E ⊆ T → ∀ k : Fin (t + 1), E.card = m * k →
      eval ((E : Set (Fin n)).indicator 1) P = (Pi.single 0 1 : Fin (t + 1) → K) k := by
    intro E hE k hk
    rw [← hc, hP, map_sum]
    simp only [map_mul, eval_C, eval_esymmOn K hE, hk, Matrix.mulVec, dotProduct, hBK,
      Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨P, ?_, ?_, ?_⟩
  · refine totalDegree_finsetSum_le fun j _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_esymmOn_le K T j).trans (Nat.lt_succ_iff.mp j.isLt)
  · have h := key ∅ (empty_subset _) 0 (by simp)
    simp only [coe_empty, Set.indicator_empty, Pi.single_eq_same] at h
    exact h
  · intro E hE
    obtain ⟨hsub, k, hk1, hkt, hcard⟩ := isZeroSet_cubeSeq hm hn hE
    rw [key E hsub ⟨k, Nat.lt_succ_of_le hkt⟩ hcard]
    refine Pi.single_eq_of_ne (fun h => ?_) _
    have := congrArg Fin.val h
    simp only [Fin.val_zero] at this
    omega

end Sharpness

/-!
## Proof of Proposition 4.1

Proof: the sequence `U = e₁^{m-1} e₂^{m-1} e₃^{m(t+1)-1}` of length
`m(t+3) - 3` has a separator of degree `t` (`hasSeparator_cubeSeq`, built from the binomial
determinant `det_choose_mul`). Since separators pass to shorter sequences
(`exists_hasSeparator_of_le`), the characterization `kappa_eq_iff` forces
`κ_t(C_m^3; K) > m(t+3) - 3`.
-/

open Sharpness in
/-- **Proposition 4.1**: for `m ≥ 2`, `t ≥ 0` and a field `K` of
characteristic zero or of characteristic not dividing `m`, `κ_t(C_m^3;K) ≥ m(t+3) - 2`. -/
theorem le_kappa_cube (m : ℕ) [NeZero m] (hm : 2 ≤ m) (t : ℕ) (K : Type*) [Field K]
    (hK : ringChar K = 0 ∨ ¬ ringChar K ∣ m) :
    m * (t + 3) - 2 ≤ kappa (Fin 3 → ZMod m) K t := by
  have hn : m * (t + 3) - 3 = 2 * (m - 1) + (m * (t + 1) - 1) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  have hsep : ∃ u : Fin (m * (t + 3) - 3) → (Fin 3 → ZMod m), HasSeparator K u t :=
    ⟨_, hasSeparator_cubeSeq m (by omega) t K (natCast_ne_zero_of_ringChar m K hK) hn⟩
  by_contra hlt
  have hk := ((kappa_eq_iff (Fin 3 → ZMod m) K t _).mp rfl).1
  obtain ⟨u, hu⟩ := exists_hasSeparator_of_le K (N' := kappa (Fin 3 → ZMod m) K t) (by omega) hsep
  exact hk u hu

end DavenportProject
