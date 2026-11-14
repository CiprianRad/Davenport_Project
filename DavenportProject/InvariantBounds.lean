/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Invariants
import DavenportProject.Identities.Operations
import DavenportProject.Identities.Duality
import DavenportProject.Identities.Evaluation
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The elementary properties of the incidence threshold

The degree-zero identity `κ₀(G; K) = D(G)` is the observation in Section 1 of the paper:
the only degree-zero separator is the constant polynomial one.
-/

public section

namespace DavenportProject

open Finset MvPolynomial

/-- **Section 1, degree-zero separators**: the constant polynomial one separates precisely
the sequences with no nonempty zero set. -/
theorem hasSeparator_zero_iff {G ι : Type*} [AddCommGroup G]
    (K : Type*) [Field K] (u : ι → G) :
    HasSeparator K u 0 ↔ ∀ E, ¬ IsZeroSet u E := by
  constructor
  · rintro ⟨P, hdeg, hzero, hsets⟩ E hE
    -- A polynomial of degree zero is constant; its value at the origin fixes it to one.
    have hC := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hdeg)
    have hcoeff : P.coeff 0 = 1 := by
      rw [hC] at hzero
      simpa only [eval_C] using hzero
    have hone : P = 1 := by rw [hC, hcoeff, C_1]
    have hbad := hsets E hE
    rw [hone, map_one] at hbad
    exact one_ne_zero hbad
  · intro h
    -- Conversely, the vanishing conditions are empty for a zero-sum-free sequence.
    refine ⟨1, by simp, by simp, fun E hE => ?_⟩
    exact (h E hE).elim

/-- **Section 1, the degree-zero incidence threshold**: `κ₀(G; K) = D(G)`.
This is the paper's constant-separator argument, followed by the two minimum characterizations. -/
theorem kappa_zero_eq_davenport (G : Type*) [AddCommGroup G] [Finite G]
    (K : Type*) [Field K] : kappa G K 0 = davenport G := by
  apply (kappa_eq_iff G K 0 (davenport G)).2
  obtain ⟨hforce, hminimal⟩ := (davenport_eq_iff G (davenport G)).1 rfl
  constructor
  · intro u hsep
    obtain ⟨E, hE⟩ := hforce u
    exact (hasSeparator_zero_iff K u).1 hsep E hE
  · intro N hN
    obtain ⟨u, hu⟩ := hminimal N hN
    exact ⟨u, (hasSeparator_zero_iff K u).2 hu⟩

/-- **Section 2, finiteness of the incidence threshold**: consecutive blocks of `D(G)`
positions supply `t + 1` disjoint zero sets and hence an integral identity of degree `t`. -/
theorem hasIncidenceIdentity_mul_davenport (G : Type*) [AddCommGroup G] [Finite G]
    (t : ℕ) (u : Fin ((t + 1) * davenport G) → G) : HasIncidenceIdentity ℤ u t := by
  -- Each block contains a zero set by the defining property of the Davenport constant.
  let L := davenport G
  have hL : ∀ v : Fin L → G, ∃ E, IsZeroSet v E :=
    ((davenport_eq_iff G (davenport G)).1 rfl).1
  let e : Fin (t + 1) → Fin L ↪ Fin ((t + 1) * L) := fun k =>
    ⟨fun j => finProdFinEquiv (k, j), fun a b h => by
      simpa using finProdFinEquiv.injective h⟩
  choose E hE using fun k : Fin (t + 1) => hL (fun j => u (e k j))
  let B : Fin (t + 1) → Finset (Fin ((t + 1) * L)) := fun k => (E k).map (e k)
  have hB : ∀ k, IsZeroSet u (B k) := fun k =>
    ⟨(hE k).1.map, by simpa [B, Finset.sum_map] using (hE k).2⟩
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro k l hkl
    simp only [Function.onFun, B, Finset.disjoint_left, Finset.mem_map]
    rintro _ ⟨a, -, rfl⟩ ⟨b, -, hb⟩
    have := finProdFinEquiv.injective hb
    exact hkl (Prod.ext_iff.mp this).1.symm
  -- Lemma 2.2(1) assigns the inclusion–exclusion weights to their unions.
  exact hasIncidenceIdentity_of_pairwise_disjoint u t B hB hdisj

/-- **Section 2, finiteness bound**: `κ_t(G; K) ≤ (t + 1) D(G)`.
The paper extracts disjoint zero sets in blocks of `D(G)` positions and uses Lemma 2.2(1). -/
theorem kappa_le_mul_davenport (G : Type*) [AddCommGroup G] [Finite G]
    (K : Type*) [Field K] (t : ℕ) : kappa G K t ≤ (t + 1) * davenport G := by
  by_contra hlt
  push Not at hlt
  obtain ⟨u, hsep⟩ := ((kappa_eq_iff G K t (kappa G K t)).1 rfl).2 _ hlt
  obtain ⟨c, hc⟩ := hasIncidenceIdentity_mul_davenport G t u
  -- Reduce the integral weights to K, then use the alternative of Lemma 2.1(3).
  exact (hasIncidenceIdentity_iff_not_hasSeparator K u t).1 ⟨_, hc.intCast K⟩ hsep

end DavenportProject
