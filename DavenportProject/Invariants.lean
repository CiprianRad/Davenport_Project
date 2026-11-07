/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Defs
import DavenportProject.Identities.Duality
import DavenportProject.Identities.Evaluation
import DavenportProject.Identities.Operations
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The Davenport constant and `κ_t`

* `davenport G`: the least `N` such that every sequence of `N` terms has a zero set, defined from
  `exists_length_forcing_zeroSet` and characterized by `davenport_eq_iff`.
* `kappa G K t`: the least `N` such that no sequence of `N` terms has a separator of degree `t`
  over `K`, defined from `exists_length_without_separator` and characterized by `kappa_eq_iff`.
-/

@[expose] public section

namespace DavenportProject

open Finset

-- Not used below, but it fixes the universe names of `davenport` and `kappa`, which enter their
-- hashes in `statements.json`.
variable {G : Type*} [AddCommGroup G] {ι : Type*}

/-! ## The Davenport constant `D(G)` -/

/-- Every long enough sequence has a zero set; this makes `davenport` well defined. -/
theorem exists_length_forcing_zeroSet (G : Type*) [AddCommGroup G] [Finite G] :
    ∃ L : ℕ, ∀ u : Fin L → G, ∃ E, IsZeroSet u E := by
  classical
  have := Fintype.ofFinite G
  refine ⟨Fintype.card G, fun u => ?_⟩
  set s : Fin (Fintype.card G + 1) → G := fun k => ∑ i with i.val < k.val, u i with hs
  obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt s (by simp)
  -- reduce to `j < k` with `s j = s k`
  have key : ∀ j k : Fin (Fintype.card G + 1), j < k → s j = s k →
      ∃ E, IsZeroSet u E := by
    intro j k hjk hjk'
    refine ⟨univ.filter fun i : Fin (Fintype.card G) => j.val ≤ i.val ∧ i.val < k.val, ?_, ?_⟩
    · have hj : j.val < Fintype.card G := by omega
      exact ⟨⟨j.val, hj⟩, by simp [hjk]⟩
    · have hsplit : s k = s j + ∑ i with j.val ≤ i.val ∧ i.val < k.val, u i := by
        simp only [hs]
        rw [← Finset.sum_filter_add_sum_filter_not
          ({i | i.val < k.val} : Finset (Fin (Fintype.card G))) (fun i => i.val < j.val)]
        congr 1
        · congr 1; ext i; simp only [mem_filter, mem_univ, true_and]; omega
        · congr 1; ext i; simp only [mem_filter, mem_univ, true_and]; omega
      rw [hjk'] at hsplit
      simpa using hsplit.symm
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h he
  · exact key b a h he.symm

open Classical in
/-- The *Davenport constant* `D(G)`: the least `L` such that every sequence of `L` terms
over `G` has a nonempty zero-sum subsequence. -/
noncomputable def davenport (G : Type*) [AddCommGroup G] [Finite G] : ℕ :=
  Nat.find (exists_length_forcing_zeroSet G)

/-- Characterization of `davenport`: every sequence of `L` terms has a zero set, and `L` is the
least such length. -/
theorem davenport_eq_iff (G : Type*) [AddCommGroup G] [Finite G] (L : ℕ) :
    davenport G = L ↔
      (∀ u : Fin L → G, ∃ E, IsZeroSet u E) ∧
        ∀ L' < L, ∃ u : Fin L' → G, ∀ E, ¬ IsZeroSet u E := by
  classical
  unfold davenport
  rw [Nat.find_eq_iff]
  simp only [not_forall, not_exists]

/-! ## The invariant `κ_t(G;K)` -/

/-- Every short enough sequence has a separator; this makes `kappa` well defined. -/
theorem exists_length_without_separator (G : Type*) [AddCommGroup G] [Finite G]
    (K : Type*) [Field K] (t : ℕ) :
    ∃ N : ℕ, ∀ u : Fin N → G, ¬ HasSeparator K u t := by
  obtain ⟨L, hL⟩ := exists_length_forcing_zeroSet G
  refine ⟨(t + 1) * L, fun u => ?_⟩
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
  obtain ⟨c, hc⟩ := hasIncidenceIdentity_of_pairwise_disjoint u t B hB hdisj
  exact (hasIncidenceIdentity_iff_not_hasSeparator K u t).mp
    ⟨_, IsIncidenceIdentity.intCast K hc⟩

open Classical in
/-- `κ_t(G;K)`: the least `N` such that no sequence of `N` terms over `G` has a separator of
degree `t` over `K`. -/
noncomputable def kappa (G : Type*) [AddCommGroup G] [Finite G] (K : Type*) [Field K]
    (t : ℕ) : ℕ :=
  Nat.find (exists_length_without_separator G K t)

/-- Characterization of `kappa`: no sequence of `L` terms has a separator of degree `t`, and `L`
is the least such length. -/
theorem kappa_eq_iff (G : Type*) [AddCommGroup G] [Finite G] (K : Type*) [Field K]
    (t N : ℕ) :
    kappa G K t = N ↔
      (∀ u : Fin N → G, ¬ HasSeparator K u t) ∧
        ∀ N' < N, ∃ u : Fin N' → G, HasSeparator K u t := by
  classical
  unfold kappa
  rw [Nat.find_eq_iff]
  simp only [not_forall, not_not]

end DavenportProject
