/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George C. Rad
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.MvPolynomial.Basic
import DavenportProject.Transfer.Augmentation

/-!
# Lemma 3.1

The statement is kept in a module of its own that does not see the field instance on `ZMod p`,
so that it elaborates exactly as the reference statement in `statements.json`: the ring
structure of `ZMod p` in `MvPolynomial (Fin N) (ZMod p)` is found through `ZMod.commRing`. The
proof is `DavenportProject.Transfer.exists_multilinear_indicator`.
-/

public section

namespace DavenportProject

open Finset

/-- **Lemma 3.1**: for `H = ⊕_{i} C_{p^{a_i}}` and `M = ∑_i (p^{a_i} - 1)`,
and arbitrary labels `v_1, …, v_N ∈ H`, the Boolean function `z ↦ 𝟙[∑_j z_j v_j = 0] ∈ 𝔽_p`
is represented by a multilinear polynomial over `𝔽_p` of degree at most `M`. -/
theorem exists_multilinear_zeroSum_indicator (p : ℕ) [Fact p.Prime] {r : ℕ} (a : Fin r → ℕ)
    {N : ℕ} (v : Fin N → ((i : Fin r) → ZMod (p ^ a i))) :
    ∃ P : MvPolynomial (Fin N) (ZMod p),
      P ∈ MvPolynomial.restrictDegree (Fin N) (ZMod p) 1 ∧
      P.totalDegree ≤ ∑ i, (p ^ a i - 1) ∧
      ∀ E : Finset (Fin N),
        MvPolynomial.eval ((E : Set (Fin N)).indicator 1) P =
          if ∑ j ∈ E, v j = 0 then 1 else 0 :=
  Transfer.exists_multilinear_indicator

end DavenportProject

end
