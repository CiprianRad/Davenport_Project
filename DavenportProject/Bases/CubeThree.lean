/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George C. Rad
-/
module

public import DavenportProject.Defs
public import Mathlib.Data.ZMod.Basic
import DavenportProject.Bases.Basic
import DavenportProject.Bases.CubeThree.Identity
import DavenportProject.Bases.CubeThree.LongZeroSet
import DavenportProject.Identities.Operations
import DavenportProject.Invariants

/-!
# Theorem B for `m = 3`

`hasIncidenceIdentity_cube_three`: every sequence of `3t + 7` terms over `C_3^3` has an integral
`𝓘_t`-identity, from Lemmas 5.1 and 5.2, `η(C_3^3) ≤ 17` and Lemma 2.2.
-/

/-!
## Short zero sets over `C_3^3`

A short-zero-free sequence over `C_3^3` has every multiplicity at most two (three equal terms
sum to zero) and, by Lemma 5.1(2), a support of at most eight points. So it has at most
sixteen terms: `η(C_3^3) ≤ 17` (`not_isShortZeroFree_cube_three`).
-/

public section

namespace DavenportProject.Bases

open Finset DavenportProject
open DavenportProject.CubeThree
  (allowed_image allowed_spec card_filter_le_two)

/-- `η(C_3^3) ≤ 17`: every seventeen terms over `C_3^3` contain a zero
set of size at most `exp = 3`. -/
theorem not_isShortZeroFree_cube_three (u : Fin 17 → (Fin 3 → ZMod 3)) :
    ¬ IsShortZeroFree u := by
  intro hu
  have h8 := (allowed_spec (allowed_image hu)).1
  have h17 := card_eq_sum_card_image u univ
  rw [card_univ, Fintype.card_fin] at h17
  have hle : ∑ x ∈ univ.image u, #{i ∈ univ | u i = x} ≤ ∑ _x ∈ univ.image u, 2 :=
    sum_le_sum fun x _ => card_filter_le_two hu x
  rw [sum_const, smul_eq_mul] at hle
  omega

end DavenportProject.Bases

end

/-!
## Theorem B for `m = 3`

Every sequence of `3t + 7` terms over `C_3^3` has an integral `𝓘_t`-identity, by induction on
`t` over an arbitrary index type of that cardinality:
* `t = 0`: a zero set exists since `D(C_3^3) = 7`; apply Lemma 2.2(1).
* `t ≥ 1`, with a zero set `B` of size at most three: `3t + 4` of the remaining terms have an
  `𝓘_{t-1}`-identity by induction; apply Lemma 2.2(2).
* otherwise the sequence is short-zero-free, and
  * `t = 1`: ten terms, Lemma 5.1(1);
  * `t = 2`: thirteen terms, Lemma 5.2 gives a zero set of size at least eleven, which properly
    contains ten indices; apply Lemma 2.2(3);
  * `t = 3`: sixteen terms, every point of an eight-point support occurs twice, so the whole
    sequence is a zero set properly containing thirteen indices; apply Lemma 2.2(3);
  * `t ≥ 4`: impossible, since `η(C_3^3) ≤ 17`.
-/

public section

namespace DavenportProject.Bases

open Finset DavenportProject
open DavenportProject.CubeThree
  (allowed_image allowed_spec card_filter_le_two exponent_eq_three)

/-- A sequence over `C_3^3` that is not short-zero-free has a zero set of size at most three. -/
theorem exists_isZeroSet_card_le_three {ι : Type*} {u : ι → (Fin 3 → ZMod 3)}
    (hu : ¬ IsShortZeroFree u) : ∃ B, IsZeroSet u B ∧ #B ≤ 3 := by
  simp only [IsShortZeroFree, exponent_eq_three, not_forall, not_lt] at hu
  obtain ⟨B, hB, hc⟩ := hu
  exact ⟨B, hB, hc⟩

/-- Seventeen or more terms over `C_3^3` are never short-zero-free. -/
theorem not_isShortZeroFree_of_le_card {ι : Type*} [Fintype ι] (u : ι → (Fin 3 → ZMod 3))
    (h : 17 ≤ Fintype.card ι) : ¬ IsShortZeroFree u := by
  intro hu
  have f : Fin 17 ↪ ι :=
    (Fin.castLEEmb h).trans (Fintype.equivFin ι).symm.toEmbedding
  exact not_isShortZeroFree_cube_three _ (isShortZeroFree_comp_embedding hu f)

/-- sixteen short-zero-free terms over `C_3^3` sum to zero, because every
point of the (eight-point) support occurs exactly twice. -/
theorem sum_eq_zero_of_isShortZeroFree_sixteen (v : Fin 16 → (Fin 3 → ZMod 3))
    (hv : IsShortZeroFree v) : ∑ i, v i = 0 := by
  classical
  have hspec := allowed_spec (allowed_image hv)
  have h16 := card_eq_sum_card_image v univ
  rw [card_univ, Fintype.card_fin] at h16
  have hle : ∀ x ∈ univ.image v, #{i ∈ univ | v i = x} ≤ 2 := fun x _ => card_filter_le_two hv x
  have hsum : ∑ x ∈ univ.image v, #{i ∈ univ | v i = x} ≤ ∑ _x ∈ univ.image v, 2 :=
    sum_le_sum hle
  rw [sum_const, smul_eq_mul] at hsum
  have h8 : #(univ.image v) = 8 := by omega
  have heq : ∑ x ∈ univ.image v, #{i ∈ univ | v i = x} = ∑ _x ∈ univ.image v, 2 := by
    rw [sum_const, smul_eq_mul]
    omega
  have h2 := (sum_eq_sum_iff_of_le hle).1 heq
  calc ∑ i, v i = ∑ i, id (v i) := rfl
    _ = ∑ x ∈ univ.image v, #{i ∈ univ | v i = x} • id x := sum_comp id v
    _ = ∑ x ∈ univ.image v, 2 • x := sum_congr rfl fun x hx => by rw [h2 x hx]; rfl
    _ = 0 := by rw [← smul_sum, hspec.2.2 h8, smul_zero]

/-- Degree zero: seven terms over `C_3^3` have an integral `𝓘_0`-identity (`D(C_3^3) = 7`). -/
theorem hasIncidenceIdentity_zero_of_card_eq_seven {ι : Type*} [Fintype ι]
    (h : Fintype.card ι = 7) (u : ι → (Fin 3 → ZMod 3)) : HasIncidenceIdentity ℤ u 0 := by
  let e : ι ≃ Fin 7 := Fintype.equivFinOfCardEq h
  obtain ⟨E, hE⟩ :=
    ((davenport_eq_iff _ 7).1 davenport_cube_three).1 (fun k => u (e.symm k))
  have hB : IsZeroSet u (E.map e.symm.toEmbedding) := (isZeroSet_map_equiv u e.symm E).2 hE
  exact hasIncidenceIdentity_of_pairwise_disjoint u 0 (fun _ => E.map e.symm.toEmbedding)
    (fun _ => hB) (fun i j hij => absurd (Subsingleton.elim (α := Fin 1) i j) hij)

/-- Lemma 2.2(3) applied to a zero set `Z` of size larger than `n`, with an identity of degree
`t - 1` on every `n` indices. -/
theorem hasIncidenceIdentity_of_card_lt_zeroSet {ι : Type} [Fintype ι]
    (u : ι → (Fin 3 → ZMod 3)) {t n : ℕ} (ht : 1 ≤ t) (Z : Finset ι) (hZ : IsZeroSet u Z)
    (hn : n < #Z)
    (ih : ∀ (κ : Type) [Fintype κ], Fintype.card κ = n →
      ∀ w : κ → (Fin 3 → ZMod 3), HasIncidenceIdentity ℤ w (t - 1)) :
    HasIncidenceIdentity ℤ u t := by
  obtain ⟨T, hTZ, hT⟩ := exists_subset_card_eq hn.le
  have hss : T ⊂ Z := hTZ.ssubset_of_ne (by rintro rfl; omega)
  exact hasIncidenceIdentity_of_ssubset_zeroSet u ht Z T hZ hss
    (ih T (by rw [Fintype.card_coe, hT]) _)

/-- Theorem B for `m = 3`, over an arbitrary index type with `3t + 7` positions. -/
theorem hasIncidenceIdentity_cube_three_of_card (t : ℕ) :
    ∀ (ι : Type) [Fintype ι], Fintype.card ι = 3 * t + 7 →
      ∀ u : ι → (Fin 3 → ZMod 3), HasIncidenceIdentity ℤ u t := by
  induction t with
  | zero =>
    intro ι _ h u
    exact hasIncidenceIdentity_zero_of_card_eq_seven h u
  | succ t ih =>
    intro ι _ h u
    classical
    by_cases hsz : IsShortZeroFree u
    · rcases t with _ | _ | _ | t
      · -- ten terms: Lemma 5.1(1)
        let e : ι ≃ Fin 10 := Fintype.equivFinOfCardEq h
        have := hasIncidenceIdentity_comp_equiv _ e
          (hasIncidenceIdentity_cube_three_ten (fun k => u (e.symm k)))
        simpa using this
      · -- thirteen terms: Lemma 5.2 and Lemma 2.2(3)
        let e : ι ≃ Fin 13 := Fintype.equivFinOfCardEq h
        obtain ⟨E, hE, hE11⟩ := exists_large_zeroSet_cube_three (fun k => u (e.symm k))
          (isShortZeroFree_comp_embedding hsz e.symm.toEmbedding)
        exact hasIncidenceIdentity_of_card_lt_zeroSet u (n := 10) (by omega) _
          ((isZeroSet_map_equiv u e.symm E).2 hE) (by rw [card_map]; omega) ih
      · -- sixteen terms: the whole sequence is a zero set; Lemma 2.2(3)
        let e : ι ≃ Fin 16 := Fintype.equivFinOfCardEq h
        have hs := sum_eq_zero_of_isShortZeroFree_sixteen (fun k => u (e.symm k))
          (isShortZeroFree_comp_embedding hsz e.symm.toEmbedding)
        have hZ : IsZeroSet u univ := by
          refine ⟨univ_nonempty_iff.2 ⟨e.symm 0⟩, ?_⟩
          rw [← hs]
          exact (Equiv.sum_comp e.symm u).symm
        exact hasIncidenceIdentity_of_card_lt_zeroSet u (n := 13) (by omega) univ hZ
          (by rw [card_univ]; omega) ih
      · -- at least nineteen terms: never short-zero-free (`η(C_3^3) ≤ 17`)
        exact absurd hsz (not_isShortZeroFree_of_le_card u (by omega))
    · -- a zero set `B` of size at most three; Lemma 2.2(2)
      obtain ⟨B, hB, hBcard⟩ := exists_isZeroSet_card_le_three hsz
      have hc : 3 * t + 7 ≤ #Bᶜ := by
        rw [card_compl]
        omega
      obtain ⟨S, hS, hScard⟩ := exists_subset_card_eq hc
      have hSB : Disjoint S B := disjoint_left.2 fun i hi => mem_compl.1 (hS hi)
      exact hasIncidenceIdentity_of_disjoint_zeroSet u (Nat.le_add_left 1 t) B S hB hSB
        (ih S (by rw [Fintype.card_coe, hScard]) _)

/-- Theorem B for `m = 3`: every sequence of `3(t+3) - 2` terms over
`C_3^3` has an integral `𝓘_t`-identity. -/
theorem hasIncidenceIdentity_cube_three (t : ℕ)
    (u : Fin (3 * (t + 3) - 2) → (Fin 3 → ZMod 3)) :
    HasIncidenceIdentity ℤ u t :=
  hasIncidenceIdentity_cube_three_of_card t _ (by rw [Fintype.card_fin]; omega) u

end DavenportProject.Bases

end
