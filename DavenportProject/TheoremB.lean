/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George C. Rad
-/
module

public import DavenportProject.Defs
public import DavenportProject.Invariants
public import Mathlib.Data.ZMod.Basic
import DavenportProject.Bases.CubeFour
import DavenportProject.Bases.CubeThree
import DavenportProject.Bases.CubeTwo
import DavenportProject.Identities.Duality
import DavenportProject.Identities.Evaluation
import DavenportProject.Sharpness

/-!
# Theorem B

For `m ∈ {2, 3, 4}` and every `t ≥ 0`, every sequence of `m(t + 3) - 2` terms over `C_m^3` has an
integral `𝓘_t`-identity (`hasIncidenceIdentity_cube`). The three cases are
`Bases.hasIncidenceIdentity_cube_two`, `Bases.hasIncidenceIdentity_cube_three` and
`Bases.hasIncidenceIdentity_cube_four` (Section 5 of the paper).

Consequently `κ_t(C_m^3; K) ≤ m(t + 3) - 2` for every field `K` (`kappa_cube_le`), with equality
when the characteristic of `K` is zero or does not divide `m` (`kappa_cube_eq`, using the lower
bound of Proposition 4.1, `le_kappa_cube`).
-/

public section

namespace DavenportProject.Bases

variable {G : Type*} [AddCommGroup G]

/-- An integral `𝓘_t`-identity for every sequence of length `N` gives `κ_t(G; K) ≤ N` for every
field `K`: the identity reduces to an identity over `K` (Lemma 2.1(2)), which rules out a separator
of degree `t` (Lemma 2.1(3)), while `κ_t(G; K) > N` would give a sequence of length `N` with a
separator. -/
theorem kappa_le_of_forall_hasIncidenceIdentity [Finite G] (K : Type*) [Field K]
    {t N : ℕ} (h : ∀ u : Fin N → G, HasIncidenceIdentity ℤ u t) :
    kappa G K t ≤ N := by
  by_contra hlt
  push Not at hlt
  obtain ⟨-, hmin⟩ := (kappa_eq_iff G K t (kappa G K t)).mp rfl
  obtain ⟨u, hsep⟩ := hmin N hlt
  obtain ⟨c, hc⟩ := h u
  exact (hasIncidenceIdentity_iff_not_hasSeparator K u t).mp ⟨_, hc.intCast K⟩ hsep

end DavenportProject.Bases

namespace DavenportProject

open Finset

/-- **Theorem B**, first sentence: for `m ∈ {2,3,4}` and `t ≥ 0`, every
indexed sequence of `m(t+3) - 2` terms over `C_m^3` has an integral `𝓘_t`-identity. -/
theorem hasIncidenceIdentity_cube (m : ℕ) (hm : m = 2 ∨ m = 3 ∨ m = 4) (t : ℕ)
    (u : Fin (m * (t + 3) - 2) → (Fin 3 → ZMod m)) :
    HasIncidenceIdentity ℤ u t := by
  rcases hm with rfl | rfl | rfl
  · exact Bases.hasIncidenceIdentity_cube_two t u
  · exact Bases.hasIncidenceIdentity_cube_three t u
  · exact Bases.hasIncidenceIdentity_cube_four t u

/-- **Theorem B**, second sentence, upper bound:
`κ_t(C_m^3;K) ≤ m(t+3) - 2` for every field `K`. -/
theorem kappa_cube_le (m : ℕ) [NeZero m] (hm : m = 2 ∨ m = 3 ∨ m = 4) (t : ℕ)
    (K : Type*) [Field K] :
    kappa (Fin 3 → ZMod m) K t ≤ m * (t + 3) - 2 :=
  Bases.kappa_le_of_forall_hasIncidenceIdentity K (hasIncidenceIdentity_cube m hm t)

/-- **Theorem B**, second sentence, sharpness: equality whenever the
characteristic of `K` is zero or does not divide `m` (with Proposition 4.1). -/
theorem kappa_cube_eq (m : ℕ) [NeZero m] (hm : m = 2 ∨ m = 3 ∨ m = 4) (t : ℕ)
    (K : Type*) [Field K] (hK : ringChar K = 0 ∨ ¬ ringChar K ∣ m) :
    kappa (Fin 3 → ZMod m) K t = m * (t + 3) - 2 := by
  have h2 : 2 ≤ m := by omega
  exact le_antisymm (kappa_cube_le m hm t K) (le_kappa_cube m h2 t K hK)

end DavenportProject

end
