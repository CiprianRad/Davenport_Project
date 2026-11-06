/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George C. Rad
-/
module

public import DavenportProject.Defs
public import DavenportProject.Invariants
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.MvPolynomial.Basic
import DavenportProject.Identities.Duality
import DavenportProject.Identities.Evaluation
import DavenportProject.Transfer.Indicator
import DavenportProject.Transfer.Olson
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Theorem A: the transfer principle

* `davenport_prod_le_of_hasIncidenceIdentity_zmod` (Theorem A): if every sequence of `L(t)` terms
  over `Q` has an `𝓘_t`-identity over `ZMod p`, then `D(Q ⊕ H) ≤ L(D(H) - 1)` for every finite
  abelian `p`-group `H`.
* `davenport_prod_le_of_hasIncidenceIdentity_int`: the same for integral identities, for every
  prime `p`.

The proof uses Lemma 3.1, Olson's theorem, Lemma 2.1(3) and the structure theorem for finite
abelian `p`-groups.
-/

/-!
## Basic API for the Davenport constant

Consequences of the characterization `davenport_eq_iff`:
* `davenport_le_of_forall`: if every `N`-term sequence has a zero set, then `D(G) ≤ N`;
* `exists_isZeroSet_of_davenport_le`: if `D(G) ≤ N`, every `N`-term sequence has a zero set;
* `davenport_congr`: the Davenport constant is invariant under additive isomorphisms.
-/

public section

namespace DavenportProject.Transfer

open Finset DavenportProject

variable {G G' : Type*} [AddCommGroup G] [Finite G] [AddCommGroup G'] [Finite G']

/-- If every sequence of `N` terms over `G` has a zero set, then `D(G) ≤ N`. -/
theorem davenport_le_of_forall {N : ℕ} (h : ∀ u : Fin N → G, ∃ E, IsZeroSet u E) :
    davenport G ≤ N := by
  by_contra hlt
  push Not at hlt
  obtain ⟨u, hu⟩ := ((davenport_eq_iff G (davenport G)).1 rfl).2 N hlt
  obtain ⟨E, hE⟩ := h u
  exact hu E hE

/-- If `D(G) ≤ N`, then every sequence of `N` terms over `G` has a zero set. -/
theorem exists_isZeroSet_of_davenport_le {N : ℕ} (h : davenport G ≤ N) (u : Fin N → G) :
    ∃ E, IsZeroSet u E := by
  obtain ⟨E, hEne, hEsum⟩ :=
    ((davenport_eq_iff G (davenport G)).1 rfl).1 (u ∘ Fin.castLE h)
  refine ⟨E.map (Fin.castLEEmb h), hEne.map, ?_⟩
  rw [Finset.sum_map]
  exact hEsum

omit [Finite G] [Finite G'] in
/-- Zero sets transport along additive isomorphisms. -/
theorem isZeroSet_comp_iff {ι : Type*} (e : G ≃+ G') (u : ι → G) (E : Finset ι) :
    IsZeroSet (fun i => e (u i)) E ↔ IsZeroSet u E := by
  unfold IsZeroSet
  rw [← map_sum, e.map_eq_zero_iff]

/-- The Davenport constant is invariant under additive isomorphisms. -/
theorem davenport_congr (e : G ≃+ G') : davenport G = davenport G' := by
  apply le_antisymm
  · refine davenport_le_of_forall fun u => ?_
    obtain ⟨E, hE⟩ := exists_isZeroSet_of_davenport_le le_rfl (fun i => e (u i))
    exact ⟨E, (isZeroSet_comp_iff e u E).1 hE⟩
  · refine davenport_le_of_forall fun u => ?_
    obtain ⟨E, hE⟩ := exists_isZeroSet_of_davenport_le le_rfl (fun i => e.symm (u i))
    exact ⟨E, (isZeroSet_comp_iff e.symm u E).1 hE⟩

end DavenportProject.Transfer

end

/-!
## Structure of finite abelian `p`-groups

A finite abelian `p`-group `H` is additively isomorphic to `∏_{i : Fin r} ZMod (p ^ a i)`
(`exists_addEquiv_pi_zmod_prime_pow`). Combined with Olson's theorem this gives
`D(H) - 1 = ∑ i, (p ^ a i - 1)` (`exists_addEquiv_pi_zmod_prime_pow_davenport`).
-/

public section

namespace DavenportProject.Transfer

open Finset DavenportProject

/-- **Structure of finite abelian `p`-groups**: a finite abelian `p`-group is additively
isomorphic to `∏_{i : Fin r} ZMod (p ^ a i)` for some `r` and `a`. -/
theorem exists_addEquiv_pi_zmod_prime_pow {p : ℕ} [hp : Fact p.Prime] {H : Type*}
    [AddCommGroup H] [Finite H] (hH : IsPGroup p (Multiplicative H)) :
    ∃ (r : ℕ) (a : Fin r → ℕ), Nonempty (H ≃+ ((i : Fin r) → ZMod (p ^ a i))) := by
  classical
  obtain ⟨ι, _, q, hq, b, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite H
  let σ := Fintype.equivFin ι
  let e₁ : H ≃+ ((j : Fin (Fintype.card ι)) → ZMod (q (σ.symm j) ^ b (σ.symm j))) :=
    e.trans ((DirectSum.linearEquivFunOnFintype ℤ ι (fun i => ZMod (q i ^ b i))).toAddEquiv.trans
      (RingEquiv.piCongrLeft' (fun i => ZMod (q i ^ b i)) σ).toAddEquiv)
  have key : ∀ j, q (σ.symm j) ^ b (σ.symm j) =
      p ^ (if q (σ.symm j) = p then b (σ.symm j) else 0) := by
    intro j
    split_ifs with h
    · rw [h]
    · rw [pow_zero]
      by_contra hne
      have hb : b (σ.symm j) ≠ 0 := by
        rintro hb
        simp [hb] at hne
      obtain ⟨k, hk⟩ := hH (Multiplicative.ofAdd (e₁.symm (Pi.single j 1)))
      have h1 : p ^ k • e₁.symm (Pi.single j 1) = 0 := by
        rw [← ofAdd_nsmul] at hk
        exact hk
      have h2 : ((p ^ k : ℕ) : ZMod (q (σ.symm j) ^ b (σ.symm j))) = 0 := by
        have := congrArg (fun x => e₁ x j) h1
        simpa [map_nsmul] using this
      rw [ZMod.natCast_eq_zero_iff] at h2
      exact h ((Nat.prime_dvd_prime_iff_eq (hq _) hp.out).1
        ((hq _).dvd_of_dvd_pow ((dvd_pow_self _ hb).trans h2)))
  exact ⟨_, _, ⟨e₁.trans (AddEquiv.piCongrRight fun j => (ZMod.ringEquivCongr (key j)).toAddEquiv)⟩⟩

/-- A finite abelian `p`-group `H ≃+ ∏ ZMod (p ^ a i)` has `D(H) - 1 = ∑ i, (p ^ a i - 1)`
(Olson's theorem transported along the structure isomorphism). -/
theorem exists_addEquiv_pi_zmod_prime_pow_davenport {p : ℕ} [Fact p.Prime] {H : Type*}
    [AddCommGroup H] [Finite H] (hH : IsPGroup p (Multiplicative H)) :
    ∃ (r : ℕ) (a : Fin r → ℕ), Nonempty (H ≃+ ((i : Fin r) → ZMod (p ^ a i))) ∧
      davenport H - 1 = ∑ i, (p ^ a i - 1) := by
  obtain ⟨r, a, ⟨e⟩⟩ := exists_addEquiv_pi_zmod_prime_pow hH
  have : ∀ i, NeZero (p ^ a i) := fun i => ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  refine ⟨r, a, ⟨e⟩, ?_⟩
  rw [davenport_congr e, davenport_pi_zmod_prime_pow p a, Nat.add_sub_cancel_left]

end DavenportProject.Transfer

end

public section

namespace DavenportProject

open Finset DavenportProject
open DavenportProject.Transfer

open Finset

/-- **Theorem A** (transfer principle): if every sequence of `L(t)` terms
over `Q` has an `𝓘_t`-identity over `𝔽_p`, then `D(Q ⊕ H) ≤ L(D(H) - 1)` for every finite
abelian `p`-group `H`. -/
theorem davenport_prod_le_of_hasIncidenceIdentity_zmod (Q : Type*) [AddCommGroup Q]
    [Finite Q] (p : ℕ) [Fact p.Prime] (L : ℕ → ℕ)
    (hL : ∀ t, ∀ u : Fin (L t) → Q, HasIncidenceIdentity (ZMod p) u t)
    (H : Type*) [AddCommGroup H] [Finite H] (hH : IsPGroup p (Multiplicative H)) :
    davenport (Q × H) ≤ L (davenport H - 1) := by
  obtain ⟨r, a, ⟨e⟩, hM⟩ := exists_addEquiv_pi_zmod_prime_pow_davenport hH
  refine davenport_le_of_forall fun w => ?_
  by_contra hw
  push Not at hw
  let u : Fin (L (davenport H - 1)) → Q := fun j => (w j).1
  obtain ⟨P, -, hdeg, heval⟩ :=
    exists_multilinear_zeroSum_indicator p a (fun j => e (w j).2)
  apply (hasIncidenceIdentity_iff_not_hasSeparator (ZMod p) u (davenport H - 1)).1
    (hL _ u)
  refine ⟨P, hdeg.trans hM.ge, ?_, fun E hE => ?_⟩
  · have h0 := heval ∅
    simpa using h0
  · rw [heval E, ite_eq_right_iff]
    intro hsum
    exfalso
    rw [← map_sum, e.map_eq_zero_iff] at hsum
    refine hw E ⟨hE.1, Prod.ext ?_ ?_⟩
    · rw [Prod.fst_sum]
      exact hE.2
    · rw [Prod.snd_sum]
      exact hsum

end DavenportProject

end

public section

namespace DavenportProject

open DavenportProject.Transfer

open Finset

/-- Theorem A, last sentence: if the identities are integral, the
conclusion holds for every prime `p`. -/
theorem davenport_prod_le_of_hasIncidenceIdentity_int (Q : Type*) [AddCommGroup Q]
    [Finite Q] (L : ℕ → ℕ) (hL : ∀ t, ∀ u : Fin (L t) → Q, HasIncidenceIdentity ℤ u t)
    (p : ℕ) [Fact p.Prime]
    (H : Type*) [AddCommGroup H] [Finite H] (hH : IsPGroup p (Multiplicative H)) :
    davenport (Q × H) ≤ L (davenport H - 1) :=
  davenport_prod_le_of_hasIncidenceIdentity_zmod Q p L
    (fun t u => (hL t u).elim fun _ hc => ⟨_, hc.intCast (ZMod p)⟩) H hH

end DavenportProject

end
