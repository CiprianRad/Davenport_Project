/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Transfer.TheoremA
import DavenportProject.Identities.Operations
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Remark 3.2: the elementary block bound

The short-zero threshold `eta G` is the least length forcing a nonempty zero set
of size at most the exponent. Repeated extraction at length `eta G + t * exp(G)`
gives `t+1` disjoint short zero sets. Lemma 2.2(1) then supplies an integral
incidence identity; Theorem A gives the paper's block bound for a `p`-group kernel.
-/

public section

namespace DavenportProject

open Finset

/-- **Remark 3.2, existence of the short-zero threshold:** a long enough sequence
contains `exp(G)` equal terms, and those indexed terms sum to zero. -/
theorem exists_length_forcing_shortZeroSet (G : Type*) [AddCommGroup G] [Finite G] :
    ∃ N : ℕ, ∀ u : Fin N → G, ∃ E, IsZeroSet u E ∧ #E ≤ AddMonoid.exponent G := by
  classical
  let := Fintype.ofFinite G
  let e := AddMonoid.exponent G
  have he : 0 < e := Nat.pos_of_ne_zero AddMonoid.exponent_ne_zero_of_finite
  refine ⟨Fintype.card G * e, fun u => ?_⟩
  -- Pigeonhole: some value occurs in at least e indexed positions.
  have hex : ∃ g : G, e ≤ #(univ.filter fun i => u i = g) := by
    by_contra h
    push Not at h
    have hcount : ∑ g : G, #(univ.filter fun i => u i = g) = Fintype.card G * e := by
      simpa using (card_eq_sum_card_fiberwise
        (s := univ) (t := univ) (f := u) (fun _ _ => mem_univ _)).symm
    have hlt : (∑ g : G, #(univ.filter fun i => u i = g)) < ∑ _g : G, e :=
      sum_lt_sum (fun g _ => (h g).le) ⟨0, mem_univ _, h 0⟩
    simp [hcount] at hlt
  obtain ⟨g, hg⟩ := hex
  obtain ⟨E, hEsub, hEcard⟩ := exists_subset_card_eq hg
  refine ⟨E, ⟨card_pos.mp (by rw [hEcard]; exact he), ?_⟩, hEcard.le⟩
  calc
    ∑ i ∈ E, u i = ∑ _i ∈ E, g :=
      sum_congr rfl fun i hi => (mem_filter.mp (hEsub hi)).2
    _ = e • g := by rw [sum_const, hEcard]
    _ = 0 := AddMonoid.exponent_nsmul_eq_zero g

open Classical in
/-- **Remark 3.2, the short-zero threshold `η(G)`:** the least length such that every
sequence has a nonempty zero set of size at most `exp(G)`. -/
noncomputable def eta (G : Type*) [AddCommGroup G] [Finite G] : ℕ :=
  Nat.find (exists_length_forcing_shortZeroSet G)

/-- The forcing and minimality characterization of the paper's invariant `η(G)`. -/
theorem eta_eq_iff (G : Type*) [AddCommGroup G] [Finite G] (N : ℕ) :
    eta G = N ↔
      (∀ u : Fin N → G, ∃ E, IsZeroSet u E ∧ #E ≤ AddMonoid.exponent G) ∧
        ∀ N' < N, ∃ u : Fin N' → G,
          ∀ E, ¬ (IsZeroSet u E ∧ #E ≤ AddMonoid.exponent G) := by
  classical
  unfold eta
  rw [Nat.find_eq_iff]
  simp only [not_forall, not_exists]

namespace Transfer

/-- A sequence of at least `η(G)` indexed terms has a short zero set. -/
theorem exists_shortZeroSet_of_eta_le {G ι : Type*} [AddCommGroup G] [Finite G]
    [Fintype ι] (u : ι → G) (h : eta G ≤ Fintype.card ι) :
    ∃ E, IsZeroSet u E ∧ #E ≤ AddMonoid.exponent G := by
  let e : Fin (eta G) ↪ ι :=
    (Fin.castLEEmb h).trans (Fintype.equivFin ι).symm.toEmbedding
  obtain ⟨E, hE, hcard⟩ := ((eta_eq_iff G (eta G)).mp rfl).1 (fun i => u (e i))
  refine ⟨E.map e, ⟨hE.1.map, ?_⟩, ?_⟩
  · simpa [sum_map, e] using hE.2
  · simpa only [card_map] using hcard

/-- The same extraction inside a specified set of the original positions. -/
theorem exists_shortZeroSet_subset {G ι : Type*} [AddCommGroup G] [Finite G]
    (u : ι → G) (S : Finset ι) (h : eta G ≤ #S) :
    ∃ E ⊆ S, IsZeroSet u E ∧ #E ≤ AddMonoid.exponent G := by
  classical
  obtain ⟨E, hE, hcard⟩ := exists_shortZeroSet_of_eta_le (fun i : S => u i)
    (by simpa using h)
  let e : S ↪ ι := Function.Embedding.subtype (· ∈ S)
  refine ⟨E.map e, ?_, ⟨hE.1.map, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
    exact i.2
  · simpa [sum_map, e] using hE.2
  · simpa only [card_map] using hcard

/-- **Remark 3.2, Section 3:** repeated extraction gives `t+1` pairwise disjoint
short zero sets from `η(G)+t exp(G)` available positions. -/
theorem exists_disjoint_shortZeroSets (G : Type*) [AddCommGroup G] [Finite G] (t : ℕ) :
    ∀ {ι : Type*} (u : ι → G) (S : Finset ι),
      eta G + t * AddMonoid.exponent G ≤ #S →
      ∃ B : Fin (t + 1) → Finset ι,
        (∀ k, B k ⊆ S ∧ IsZeroSet u (B k) ∧ #(B k) ≤ AddMonoid.exponent G) ∧
        Pairwise (Function.onFun Disjoint B) := by
  induction t with
  | zero =>
    intro ι u S h
    obtain ⟨E, hES, hE, hcard⟩ := exists_shortZeroSet_subset u S (by simpa using h)
    exact ⟨fun _ => E, fun _ => ⟨hES, hE, hcard⟩,
      fun i j hij => (hij (Subsingleton.elim (α := Fin 1) i j)).elim⟩
  | succ t ih =>
    intro ι u S h
    classical
    -- Extract one short zero set. Deleting it spends at most exp(G) positions.
    obtain ⟨E, hES, hE, hcard⟩ := exists_shortZeroSet_subset u S (by omega)
    have hrest : eta G + t * AddMonoid.exponent G ≤ #(S \ E) := by
      rw [card_sdiff_of_subset hES]
      rw [Nat.succ_mul] at h
      omega
    obtain ⟨B, hB, hdisj⟩ := ih u (S \ E) hrest
    have hEB (k) : Disjoint E (B k) := by
      apply disjoint_left.mpr
      intro x hxE hxB
      exact (mem_sdiff.mp ((hB k).1 hxB)).2 hxE
    -- Keep indexed occurrences: each new block lies in the remaining positions.
    refine ⟨Fin.cons E B, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · exact ⟨hES, hE, hcard⟩
      · exact ⟨(hB k).1.trans sdiff_subset, (hB k).2⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro hne
          exact (hne rfl).elim
        · intro _
          exact hEB j
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          exact (hEB i).symm
        · intro hne
          exact hdisj (fun h => hne (congrArg Fin.succ h))

end Transfer

/-- **Remark 3.2, Section 3:** inclusion–exclusion on the repeatedly extracted
short zero sets gives the integral incidence identity at `η(G)+t exp(G)`. -/
theorem hasIncidenceIdentity_eta_add_mul_exponent (G : Type*) [AddCommGroup G] [Finite G]
    (t : ℕ) (u : Fin (eta G + t * AddMonoid.exponent G) → G) :
    HasIncidenceIdentity ℤ u t := by
  obtain ⟨B, hB, hdisj⟩ := Transfer.exists_disjoint_shortZeroSets G t u univ (by simp)
  exact hasIncidenceIdentity_of_pairwise_disjoint u t B (fun k => (hB k).2.1) hdisj

/-- **Remark 3.2, Section 3, equation (1.2):** for a finite abelian `p`-group kernel,
Theorem A recovers `D(Q ⊕ H) ≤ η(Q) + (D(H)-1) exp(Q)` from the disjoint-block identities. -/
theorem davenport_prod_le_eta_add_mul_exponent (Q : Type*) [AddCommGroup Q] [Finite Q]
    (p : ℕ) [Fact p.Prime] (H : Type*) [AddCommGroup H] [Finite H]
    (hH : IsPGroup p (Multiplicative H)) :
    davenport (Q × H) ≤ eta Q + (davenport H - 1) * AddMonoid.exponent Q := by
  -- The integral identity works for every prime after reduction of its coefficients.
  exact davenport_prod_le_of_hasIncidenceIdentity_int Q
    (fun t => eta Q + t * AddMonoid.exponent Q)
    (hasIncidenceIdentity_eta_add_mul_exponent Q) p H hH

end DavenportProject
