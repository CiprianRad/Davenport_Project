/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Defs
import DavenportProject.Identities.Operations
import Mathlib.Data.Finset.Preimage

/-! # Section 2: extending an identity from a subsequence

The paper extends an identity by putting zero weight on all other zero sets.
An embedding of finite index types preserves the indexed occurrences, including equal values.
-/

public section

namespace DavenportProject

open Finset Identities

/-- **Section 2, inheritance by longer sequences**: an incidence identity on any indexed
subsequence extends to the whole sequence by zero outside the mapped zero sets. -/
theorem HasIncidenceIdentity.of_embedding {G ι ι' R : Type*} [AddCommGroup G]
    [Fintype ι] [Fintype ι'] [CommRing R] {t : ℕ} (u : ι → G) (e : ι' ↪ ι)
    (h : HasIncidenceIdentity R (fun i => u (e i)) t) : HasIncidenceIdentity R u t := by
  classical
  obtain ⟨c, hc⟩ := h
  let Z := zeroSets (fun i => u (e i))
  -- Send each indexed zero set into the full sequence; all remaining weights are zero.
  have hmap : ∀ E ∈ Z, E.map e ∈ zeroSets u := by
    intro E hE
    have hz := mem_zeroSets.1 hE
    exact mem_zeroSets.2 ⟨hz.1.map, by simpa only [sum_map] using hz.2⟩
  let c' : Finset ι → R := fun F => ∑ E ∈ Z, if E.map e = F then c E else 0
  have reweight (f : Finset ι → R) :
      ∑ F ∈ zeroSets u, c' F * f F = ∑ E ∈ Z, c E * f (E.map e) :=
    sum_mul_reweight (zeroSets u) Z (fun E => E.map e) hmap c f
  refine ⟨c', ?_, fun J hJ1 hJt => ?_⟩
  · -- The constant moment is the old total weight, namely one.
    have htotal := reweight (fun _ => 1)
    simpa only [mul_one] using htotal.trans (by simpa only [mul_one] using hc.1)
  · have hmoment := reweight (fun F => if J ⊆ F then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at hmoment
    rw [sum_filter, hmoment]
    by_cases hJ : J ⊆ univ.map e
    · -- A moment inside the subsequence is exactly its preimage moment.
      obtain ⟨K, -, rfl⟩ := subset_map_iff.1 hJ
      simp only [map_subset_map]
      rw [← sum_filter]
      exact hc.2 K (by simpa only [card_map] using hJ1)
        (by simpa only [card_map] using hJt)
    · -- A moment using an omitted position receives no weight.
      have hnone : ∀ E : Finset ι', ¬ J ⊆ E.map e := fun E h =>
        hJ (h.trans (map_subset_map.2 (subset_univ E)))
      simp only [hnone, ite_false, sum_const_zero]

end DavenportProject
