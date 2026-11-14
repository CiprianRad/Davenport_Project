/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Defs
import DavenportProject.Bases.CubeFour.Eta
import DavenportProject.Bases.CubeFour.Quaternary
import DavenportProject.Identities.Operations

/-!
# Theorem B for `m = 4`

Every sequence of `4t + 10` terms over `C_4^3` has an integral `𝓘_t`-identity
(`hasIncidenceIdentity_cube_four`), by induction on `t` over an arbitrary index type of that
cardinality (paper, Section 5.3):
* `t = 0`: a zero set exists since `D(C_4^3) = 10`; apply Lemma 2.2(1).
* `t = 1`: fourteen terms, Lemma 5.3(1).
* `t = 2`: eighteen terms, Lemma 5.3(2).
* `t ≥ 3`: at least twenty-two terms, so the sequence is not short-zero-free
  (`η(C_4^3) ≤ 22`); a zero set `B` of size at most four leaves `4(t-1) + 10` terms, which have
  an `𝓘_{t-1}`-identity by induction; apply Lemma 2.2(2).
-/

public section

namespace DavenportProject.Bases

open Finset

/-- Theorem B for `m = 4`, over an arbitrary index type with `4t + 10` positions. -/
theorem hasIncidenceIdentity_cube_four_of_card (t : ℕ) :
    ∀ (ι : Type) [Fintype ι], Fintype.card ι = 4 * t + 10 →
      ∀ u : ι → (Fin 3 → ZMod 4), HasIncidenceIdentity ℤ u t := by
  induction t with
  | zero =>
    intro ι _ h u
    exact hasIncidenceIdentity_zero_of_card_eq_ten h u
  | succ t ih =>
    intro ι _ h u
    classical
    rcases t with _ | _ | t
    · -- fourteen terms: Lemma 5.3(1)
      let e : ι ≃ Fin 14 := Fintype.equivFinOfCardEq h
      have := hasIncidenceIdentity_comp_equiv _ e
        (hasIncidenceIdentity_cube_four_fourteen (fun k => u (e.symm k)))
      simpa using this
    · -- eighteen terms: Lemma 5.3(2)
      let e : ι ≃ Fin 18 := Fintype.equivFinOfCardEq h
      have := hasIncidenceIdentity_comp_equiv _ e
        (hasIncidenceIdentity_cube_four_eighteen (fun k => u (e.symm k)))
      simpa using this
    · -- at least twenty-two terms: a zero set `B` of size at most four; Lemma 2.2(2)
      obtain ⟨B, hB, hBcard⟩ := exists_isZeroSet_card_le_four_of_le_card u (by omega)
      have hc : 4 * (t + 2) + 10 ≤ #Bᶜ := by
        rw [card_compl]
        omega
      obtain ⟨S, hS, hScard⟩ := exists_subset_card_eq hc
      have hSB : Disjoint S B := disjoint_left.2 fun i hi => mem_compl.1 (hS hi)
      exact hasIncidenceIdentity_of_disjoint_zeroSet u (Nat.le_add_left 1 (t + 2)) B S hB hSB
        (ih S (by rw [Fintype.card_coe, hScard]) _)

/-- Theorem B for `m = 4`: every sequence of `4(t+3) - 2` terms over `C_4^3` has an integral
`𝓘_t`-identity. -/
theorem hasIncidenceIdentity_cube_four (t : ℕ) (u : Fin (4 * (t + 3) - 2) → (Fin 3 → ZMod 4)) :
    HasIncidenceIdentity ℤ u t :=
  hasIncidenceIdentity_cube_four_of_card t _ (by rw [Fintype.card_fin]; omega) u

end DavenportProject.Bases
