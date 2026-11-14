/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Bases.CubeFour.Codes
public import DavenportProject.Identities.Operations
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! # Section 5.3: the printed eighteen-term example

Positions below are numbered from zero. The five-set affine identity on the thirteen-term
complement of `B` lifts through Lemma 2.2(2). All finite checks here use the kernel.
-/

public section

namespace DavenportProject.QuaternaryExample

open Finset CubeFour

/-- Section 5.3's sequence, in the base-four coding of the certificate checker. -/
def codes : Fin 18 → ℕ := ![1,1,1,4,4,4,5,5,5,16,16,16,17,17,17,29,29,29]

/-- `U=(100)³(010)³(110)³(001)³(101)³(131)³`, in exactly the paper's order. -/
def sequence (i : Fin 18) : Fin 3 → ZMod 4 := dec 4 (codes i)

def B : Finset (Fin 18) := {8,10,12,13,15}
def A : Finset (Fin 18) := {0,1,3,4,6,7}
def C : Finset (Fin 18) := {2,7,9,11,14,17}
def D : Finset (Fin 18) := {5,6,11,14,16,17}
def C' : Finset (Fin 18) := {3,4,5,6,7,9,11,14,17}
def D' : Finset (Fin 18) := {0,1,2,6,7,11,14,16,17}

/-- **Section 5.3 example**: its total sum is `(0,3,1)`. -/
theorem sum_sequence : ∑ i, sequence i = ![0,3,1] := by decide +kernel

/-- Which of the six triples contains an indexed position. -/
def kind (i : Fin 18) : Fin 6 := ⟨i.val / 3, by omega⟩

/-- The six support values, in the printed order. -/
def point : Fin 6 → Fin 3 → ZMod 4 :=
  ![![1,0,0], ![0,1,0], ![1,1,0], ![0,0,1], ![1,0,1], ![1,3,1]]

theorem sequence_eq_point : ∀ i, sequence i = point (kind i) := by decide +kernel

/-- Multiplicity of a support value inside an arbitrary indexed subset. -/
def count (E : Finset (Fin 18)) (k : Fin 6) : ℕ := #(E.filter fun i => kind i = k)

/-- Each of the six support values occurs only three times. -/
theorem count_le_three (E : Finset (Fin 18)) (k : Fin 6) : count E k ≤ 3 := by
  have hfull : ∀ k : Fin 6, #(univ.filter fun i : Fin 18 => kind i = k) = 3 := by
    decide +kernel
  exact (card_le_card (filter_subset_filter (fun i => kind i = k) (subset_univ E))).trans_eq
    (hfull k)

/-- Counting by the six fibres retains every indexed occurrence. -/
theorem card_eq_sum_count (E : Finset (Fin 18)) : #E = ∑ k, count E k :=
  card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)

theorem sum_eq_count_point (E : Finset (Fin 18)) :
    ∑ i ∈ E, sequence i = ∑ k, count E k • point k := by
  rw [← sum_fiberwise_of_maps_to (s := E) (t := univ) (g := kind)
    (fun _ _ => mem_univ _) sequence]
  apply sum_congr rfl
  intro k hk
  calc
    ∑ i ∈ E with kind i = k, sequence i = ∑ i ∈ E with kind i = k, point k := by
      apply sum_congr rfl
      intro i hi
      rw [sequence_eq_point, (mem_filter.mp hi).2]
    _ = count E k • point k := by rw [sum_const]; rfl

/-- The three coordinate sums used in Section 5.3's short- and long-zero arguments. -/
theorem sum_coordinates (E : Finset (Fin 18)) :
    ∑ i ∈ E, sequence i =
      ![((count E 0 + count E 2 + count E 4 + count E 5 : ℕ) : ZMod 4),
        ((count E 1 + count E 2 + 3 * count E 5 : ℕ) : ZMod 4),
        ((count E 3 + count E 4 + count E 5 : ℕ) : ZMod 4)] := by
  rw [sum_eq_count_point]
  funext j
  fin_cases j <;>
    simp [point, Fin.sum_univ_succ, Finset.sum_apply, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_mul] <;> ring

/-- **Section 5.3 example**: there is no nonempty zero set with at most four positions.
The first, third and second coordinate equations force four equal terms; the six
multiplicities are each at most three. This is the paper's coordinate argument. -/
theorem no_short_zero : ∀ E : Finset (Fin 18), E.Nonempty → #E ≤ 4 →
    ∑ i ∈ E, sequence i ≠ 0 := by
  intro E hE hcard hzero
  have hcount := card_eq_sum_count E
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hcount
  change #E = count E 0 + (count E 1 + (count E 2 +
    (count E 3 + (count E 4 + (count E 5 + 0))))) at hcount
  have hpos : 0 < #E := card_pos.mpr hE
  have h0 := congrArg (fun v => v 0) hzero
  have h1 := congrArg (fun v => v 1) hzero
  have h2 := congrArg (fun v => v 2) hzero
  rw [sum_coordinates] at h0 h1 h2
  change ((count E 0 + count E 2 + count E 4 + count E 5 : ℕ) : ZMod 4) = 0 at h0
  change ((count E 1 + count E 2 + 3 * count E 5 : ℕ) : ZMod 4) = 0 at h1
  change ((count E 3 + count E 4 + count E 5 : ℕ) : ZMod 4) = 0 at h2
  rw [ZMod.natCast_eq_zero_iff] at h0 h1 h2
  have hb0 := count_le_three E 0
  have hb1 := count_le_three E 1
  have hb2 := count_le_three E 2
  have hb3 := count_le_three E 3
  have hb4 := count_le_three E 4
  have hb5 := count_le_three E 5
  have hx : count E 0 + count E 2 + count E 4 + count E 5 = 0 ∨
      count E 0 + count E 2 + count E 4 + count E 5 = 4 := by omega
  have hz : count E 3 + count E 4 + count E 5 = 0 ∨
      count E 3 + count E 4 + count E 5 = 4 := by omega
  rcases hx with hx | hx
  · have ha : count E 0 = 0 := by omega
    have hc : count E 2 = 0 := by omega
    have he : count E 4 = 0 := by omega
    have hf : count E 5 = 0 := by omega
    simp only [hc, he, hf, Nat.add_zero, Nat.mul_zero] at h1 h2
    have hb : count E 1 = 0 := Nat.eq_zero_of_dvd_of_lt h1 (by omega)
    have hd : count E 3 = 0 := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
    omega
  · have hb : count E 1 = 0 := by omega
    have hd : count E 3 = 0 := by omega
    rcases hz with hz | hz
    · have he : count E 4 = 0 := by omega
      have hf : count E 5 = 0 := by omega
      simp only [hb, hf, Nat.zero_add, Nat.mul_zero, Nat.add_zero] at h1
      have hc : count E 2 = 0 := Nat.eq_zero_of_dvd_of_lt h1 (by omega)
      omega
    · have ha : count E 0 = 0 := by omega
      have hc : count E 2 = 0 := by omega
      simp only [hb, hc, Nat.zero_add] at h1
      have hcop : Nat.Coprime 4 3 := by decide
      have hfdiv : 4 ∣ count E 5 := hcop.dvd_mul_left.mp h1
      have hf : count E 5 = 0 := Nat.eq_zero_of_dvd_of_lt hfdiv (by omega)
      omega

/-- No selection of at most three positions has the sequence's total sum `(0,3,1)`.
Its first coordinate forces the selected values to be `010` or `001`; the other
coordinates would require at least three of the former and one of the latter. -/
theorem no_small_total : ∀ E : Finset (Fin 18), #E ≤ 3 →
    ∑ i ∈ E, sequence i ≠ ![0,3,1] := by
  intro E hcard htotal
  have hcount := card_eq_sum_count E
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hcount
  change #E = count E 0 + (count E 1 + (count E 2 +
    (count E 3 + (count E 4 + (count E 5 + 0))))) at hcount
  have h0 := congrArg (fun v => v 0) htotal
  have h1 := congrArg (fun v => v 1) htotal
  have h2 := congrArg (fun v => v 2) htotal
  rw [sum_coordinates] at h0 h1 h2
  change ((count E 0 + count E 2 + count E 4 + count E 5 : ℕ) : ZMod 4) = (0 : ℕ) at h0
  change ((count E 1 + count E 2 + 3 * count E 5 : ℕ) : ZMod 4) = (3 : ℕ) at h1
  change ((count E 3 + count E 4 + count E 5 : ℕ) : ZMod 4) = (1 : ℕ) at h2
  rw [ZMod.natCast_eq_natCast_iff'] at h0 h1 h2
  have hx : count E 0 + count E 2 + count E 4 + count E 5 = 0 := by omega
  have hy : count E 1 = 3 := by omega
  have hz : count E 3 = 1 := by omega
  omega

/-- **Section 5.3 example**: there is no zero set with at least fifteen positions.
Its complement would have at most three positions and sum to the full sequence's total. -/
theorem no_long_zero : ∀ E : Finset (Fin 18), 15 ≤ #E →
    ∑ i ∈ E, sequence i ≠ 0 := by
  intro E hcard hzero
  have hcompl : #(Eᶜ) ≤ 3 := by rw [card_compl, Fintype.card_fin]; omega
  apply no_small_total Eᶜ hcompl
  have h := sum_add_sum_compl E sequence
  rw [hzero, zero_add, sum_sequence] at h
  exact h

/-- **Section 5.3 example**: three disjoint zero sets would have a zero union of
at least fifteen positions, contradicting the preceding property. -/
theorem no_three_disjoint : ¬ ∃ E F H : Finset (Fin 18),
    IsZeroSet sequence E ∧ IsZeroSet sequence F ∧ IsZeroSet sequence H ∧
    Disjoint E F ∧ Disjoint E H ∧ Disjoint F H := by
  rintro ⟨E,F,H,hE,hF,hH,hEF,hEH,hFH⟩
  have hEc : 5 ≤ #E := by
    by_contra h
    exact no_short_zero E hE.1 (by omega) hE.2
  have hFc : 5 ≤ #F := by
    by_contra h
    exact no_short_zero F hF.1 (by omega) hF.2
  have hHc : 5 ≤ #H := by
    by_contra h
    exact no_short_zero H hH.1 (by omega) hH.2
  have hUF : Disjoint (E ∪ F) H := disjoint_union_left.2 ⟨hEH,hFH⟩
  have hU := Identities.isZeroSet_union (Identities.isZeroSet_union hE hF hEF) hH hUF
  apply no_long_zero (E ∪ F ∪ H) _ hU.2
  rw [card_union_of_disjoint hUF, card_union_of_disjoint hEF]
  omega

/-- **Section 5.3 example**: the displayed set `B` is a five-term zero set. -/
theorem B_zero : IsZeroSet sequence B ∧ #B = 5 := by
  unfold IsZeroSet
  decide +kernel

/-- **Section 5.3 example**: the five displayed sets are zero sets disjoint from `B`. -/
theorem five_zero_sets : ∀ E ∈ [A,C,D,C',D'], IsZeroSet sequence E ∧ Disjoint E B := by
  intro E hE
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl <;> unfold IsZeroSet <;> decide +kernel

/-- **Section 5.3 example**: the five-set integer incidence-vector identity. -/
theorem indicator_identity : ∀ i : Fin 18,
    (if i ∈ A then (1 : ℤ) else 0) + (if i ∈ C then 1 else 0) +
      (if i ∈ D then 1 else 0) =
    (if i ∈ C' then 1 else 0) + (if i ∈ D' then 1 else 0) := by
  decide +kernel

/-- The thirteen positions outside `B`, in their original order. -/
def slots : Fin 13 → Fin 18 := ![0,1,2,3,4,5,6,7,9,11,14,16,17]

def remainderCodes : Fin 13 → ℕ := ![1,1,1,4,4,4,5,5,16,16,17,29,29]

/-- The five affine weights in the complement's thirteen-position numbering. -/
def affineCertificate : DavenportCompute.Cert :=
  [(219,1),(6020,1),(7776,1),(6136,-1),(7879,-1)]

set_option maxHeartbeats 2000000 in
-- Kernel reduction of the five affine masks and the explicit reindexing exceeds the default limit.
/-- **Section 5.3 example**: the particular thirteen-term remainder has an affine identity.
The sound certificate checker verifies the five displayed masks, with kernel evaluation. -/
theorem remainder_identity : HasIncidenceIdentity ℤ (fun i : ↥(Bᶜ) => sequence i) 1 := by
  have hc : DavenportCompute.check 4 1 (List.ofFn remainderCodes) affineCertificate = true := by
    decide +kernel
  have h := hasIncidenceIdentity_of_check remainderCodes affineCertificate hc
  have hs : ∀ j, slots j ∈ Bᶜ := by decide +kernel
  let f : Fin 13 → ↥(Bᶜ) := fun j => ⟨slots j, hs j⟩
  have hslotsinj : Function.Injective slots := by decide +kernel
  have hslotscover : ∀ i, i ∈ Bᶜ → ∃ j, slots j = i := by decide +kernel
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact hslotsinj (congrArg Subtype.val hab)
    · intro i
      obtain ⟨j, hj⟩ := hslotscover i i.property
      exact ⟨j, Subtype.ext hj⟩
  let e : Fin 13 ≃ ↥(Bᶜ) := Equiv.ofBijective f hf
  have hv : ∀ j, dec 4 (remainderCodes j) = sequence (slots j) := by decide +kernel
  have he : (fun i : ↥(Bᶜ) => sequence i) = fun i => dec 4 (remainderCodes (e.symm i)) := by
    funext i
    rw [hv]
    exact congrArg (fun j : ↥(Bᶜ) => sequence j) (e.apply_symm_apply i).symm
  rw [he]
  exact hasIncidenceIdentity_comp_equiv _ e.symm h

/-- **Section 5.3 example**: lift the remainder's affine identity by the five-term
zero set `B`, exactly as in Lemma 2.2(2). -/
theorem quadratic_identity : HasIncidenceIdentity ℤ sequence 2 :=
  hasIncidenceIdentity_of_disjoint_zeroSet sequence (by decide) B Bᶜ B_zero.1
    disjoint_compl_left remainder_identity

/-- The eleven `(mask, weight)` pairs printed in Section 3 of the supplement. -/
def quadraticCertificate : DavenportCompute.Cert :=
  [(219,1),(46336,1),(46555,-1),(150148,1),(150264,-1),(196484,-1),
   (196600,1),(215136,1),(215239,-1),(261472,-1),(261575,1)]

/-- **Supplement Section 3**: the printed eleven-set certificate independently passes
the certificate checker. The main example proof above uses the lifting construction. -/
theorem quadratic_certificate_check :
    DavenportCompute.check 4 2 (List.ofFn codes) quadraticCertificate = true := by
  decide +kernel

end DavenportProject.QuaternaryExample
