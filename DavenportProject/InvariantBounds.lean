/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Invariants

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

end DavenportProject
