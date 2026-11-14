/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Bases.CubeFour.SearchSound
public import DavenportProject.Bases.CubeFour.SearchCert
public import DavenportCompute.Checks.Roots

/-!
# The kernel checks of Lemma 5.3, assembled

The finite input of Lemma 5.3 is checked by Lean's kernel (`decide +kernel`) in the Mathlib-free
modules `DavenportCompute.Checks`: `Checks.top` (the enumeration down to the chunk roots), the
chunk checks collected in `Checks.chunks_ok`, and `Checks.topStream_roots`. With the soundness of
the enumeration (`Bases.CubeFour.SearchSound`) and of the certificate checker
(`Bases.CubeFour.SearchCert`) they give, for a sorted short-zero-free list of codes that satisfies
the guards and the multiplicity normalization:

* `identity_or_long`: for fourteen codes, an integral `𝓘_1`-identity or a zero set of at least
  eleven positions; for eighteen codes, an integral `𝓘_2`-identity or a zero set of at least
  fifteen positions.
-/

@[expose] public section

namespace DavenportProject.CubeFour

open Finset DavenportCompute DavenportCompute.Search DavenportCompute.Checks

/-- Every chunk root listed by `topStream` is checked by its chunk. -/
theorem chunk_roots_ok : ∀ t ∈ topStream, t ≠ 0 → ∃ d₁ d₂, dfs (leaf 14 1) (leaf 18 2) 3
    (Nat.sub 18 (Nat.land t 15)) ((prefixOf t).foldl step root) d₁ = some d₂ := by
  intro t ht ht0
  have hmem : t ∈ allRoots := by
    rw [← topStream_roots, List.mem_filter]
    refine ⟨ht, ?_⟩
    cases hb : Nat.beq t 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) ht0
  obtain ⟨l, hl, htl⟩ := List.mem_flatten.1 hmem
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hl
  exact chunkRun_sound (chunks_ok c hc) t htl

/-- **The finite part of Lemma 5.3.** A sorted short-zero-free list of `N = 14` (resp. `18`) codes
that satisfies the guards and the multiplicity normalization has an integral `𝓘_1`-identity
(resp. `𝓘_2`-identity) or a zero set with at least `N - 3` positions. -/
theorem identity_or_long {N t : ℕ} (hNt : (N = 14 ∧ t = 1) ∨ (N = 18 ∧ t = 2)) (c : Fin N → ℕ)
    (hsort : (List.ofFn c).Pairwise (· ≤ ·)) (hlt : ∀ y ∈ List.ofFn c, 1 ≤ y ∧ y < 64)
    (hszf : ListSZF (List.ofFn c)) (hg : Guards (List.ofFn c))
    (hn3 : n3cond (List.ofFn c).reverse = true) :
    HasIncidenceIdentity ℤ (fun k => dec 4 (c k)) t ∨
      ∃ Z : Finset (Fin N), IsZeroSet (fun k => dec 4 (c k)) Z ∧ N ≤ #Z + 3 := by
  have hpath := path_of_sorted hsort hlt hszf hg hn3
  have hgood := good_stepsFrom good_root hpath
  rw [List.nil_append] at hgood
  have hruns := leaf_of_runs top chunk_roots_ok hpath (by
    rcases hNt with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)
  obtain ⟨d₁, d₂, hleaf⟩ : ∃ d₁ d₂, leaf N t (stepsFrom root (List.ofFn c)) d₁ = some d₂ := by
    rcases hNt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hruns.1 (by simp)
    · exact hruns.2 (by simp)
  have hN : 4 ≤ N := by omega
  set st := stepsFrom root (List.ofFn c)
  change cond (long st) (some d₁) (cert N t st.q d₁) = some d₂ at hleaf
  cases hl : long st
  · rw [hl, Bool.cond_false] at hleaf
    left
    change cond (checkEntries N t st.q _) _ none = some d₂ at hleaf
    cases hc : checkEntries N t st.q (readWords (Nat.land d₁ 1048575) (Nat.shiftRight d₁ 20)).1
    · rw [hc] at hleaf; simp at hleaf
    · have hc64 : ∀ i, c i < 64 := fun i =>
        (hlt (c i) ((List.mem_ofFn' c (c i)).2 (Set.mem_range_self i))).2
      have hq : ∀ i : Fin N, st.q / 64 ^ (N - 1 - i) % 64 = c i := by
        intro i
        have := packL_div_pow (List.ofFn c) hgood.lt i (by simp)
        simpa [hgood.q] using this
      exact hasIncidenceIdentity_of_checkEntries c hc64 hq (by omega) _ hc
  · exact Or.inr (exists_long_zeroSet hN c hgood hl)

end DavenportProject.CubeFour
