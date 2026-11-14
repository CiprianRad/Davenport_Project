/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.GroupTheory.Exponent

/-!
# Zero sets, incidence identities and separators

The basic notions of the paper, for a sequence `u : ι → G` in an abelian group `G`:
* `IsZeroSet u E`, `zeroSets u`: the nonempty sets of positions with sum zero;
* `IsIncidenceIdentity R u t c`, `HasIncidenceIdentity R u t`: the `𝓘_t`-identities of eq. (1.3);
* `IsSeparator K u t P`, `HasSeparator K u t`: polynomial separators of degree at most `t`;
* `IsShortZeroFree u`: no zero set of size at most `exp(G)`.

It also contains the reindexing lemmas used throughout (`hasIncidenceIdentity_comp_equiv`,
`isZeroSet_map_equiv`, `isShortZeroFree_comp_embedding`).
-/

@[expose] public section

namespace DavenportProject

open Finset

variable {G : Type*} [AddCommGroup G] {ι : Type*}

/-- A *zero set* of the indexed sequence `u`: a nonempty set `E` of positions with
`∑ i ∈ E, u i = 0`. -/
def IsZeroSet (u : ι → G) (E : Finset ι) : Prop :=
  E.Nonempty ∧ ∑ i ∈ E, u i = 0

open Classical in
/-- The finite set `𝒵(u)` of zero sets of `u`. -/
noncomputable def zeroSets [Fintype ι] (u : ι → G) : Finset (Finset ι) :=
  univ.filter (IsZeroSet u)

open Classical in
/-- `c` is an *`𝓘_t`-identity over `R`* for `u` (eq. (1.3)): only the values of `c` on the
zero sets of `u` are read, and they satisfy `∑_E c_E = 1` and `∑_{E ⊇ J} c_E = 0` for every
`J` with `1 ≤ |J| ≤ t`. -/
def IsIncidenceIdentity (R : Type*) [CommRing R] [Fintype ι] (u : ι → G) (t : ℕ)
    (c : Finset ι → R) : Prop :=
  ∑ E ∈ zeroSets u, c E = 1 ∧
    ∀ J : Finset ι, 1 ≤ #J → #J ≤ t → ∑ E ∈ zeroSets u with J ⊆ E, c E = 0

/-- `u` has an `𝓘_t`-identity over `R`; over `R = ℤ` this is an *integral* identity. -/
def HasIncidenceIdentity (R : Type*) [CommRing R] [Fintype ι] (u : ι → G) (t : ℕ) : Prop :=
  ∃ c : Finset ι → R, IsIncidenceIdentity R u t c

/-- A *separator of degree at most `t`* over the field `K` for `u`: a polynomial of total degree at
most `t` with `P(0) = 1` and `P(𝟙_E) = 0` for every zero set `E`. -/
def IsSeparator (K : Type*) [Field K] (u : ι → G) (t : ℕ) (P : MvPolynomial ι K) : Prop :=
  P.totalDegree ≤ t ∧ MvPolynomial.eval 0 P = 1 ∧
    ∀ E : Finset ι, IsZeroSet u E → MvPolynomial.eval ((E : Set ι).indicator 1) P = 0

/-- `u` has a separator of degree at most `t` over `K`. -/
def HasSeparator (K : Type*) [Field K] (u : ι → G) (t : ℕ) : Prop :=
  ∃ P : MvPolynomial ι K, IsSeparator K u t P

/-- A sequence is *short-zero-free* if it has no zero set of size at most `exp(G)`. -/
def IsShortZeroFree (u : ι → G) : Prop :=
  ∀ E : Finset ι, IsZeroSet u E → AddMonoid.exponent G < #E

/-!
## Reindexing incidence identities

Basic transport lemmas used throughout: membership in `zeroSets`, and the invariance of
`HasIncidenceIdentity` under a reindexing of the positions by an equivalence.
-/

theorem mem_zeroSets {ι : Type*} [Fintype ι] {u : ι → G} {E : Finset ι} :
    E ∈ zeroSets u ↔ IsZeroSet u E := by
  classical
  simp [zeroSets]

/-- Zero sets transport along a reindexing `σ : ι' ≃ ι`. -/
theorem isZeroSet_map_equiv {ι ι' : Type*} (u : ι → G) (σ : ι' ≃ ι) (E : Finset ι') :
    IsZeroSet u (E.map σ.toEmbedding) ↔ IsZeroSet (fun i => u (σ i)) E := by
  simp [IsZeroSet, sum_map]

/-- Sums over zero sets transport along a reindexing `σ : ι' ≃ ι`. -/
theorem sum_zeroSets_map_equiv {R : Type*} [CommRing R] {ι ι' : Type*} [Fintype ι]
    [Fintype ι'] (u : ι → G) (σ : ι' ≃ ι) (p : Finset ι → Prop) [DecidablePred p]
    (f : Finset ι → R) :
    ∑ E ∈ zeroSets (fun i => u (σ i)) with p (E.map σ.toEmbedding), f (E.map σ.toEmbedding) =
      ∑ E ∈ zeroSets u with p E, f E := by
  refine sum_nbij' (fun E => E.map σ.toEmbedding) (fun E => E.map σ.symm.toEmbedding)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro E hE
    simp only [mem_filter, mem_zeroSets] at hE ⊢
    exact ⟨(isZeroSet_map_equiv u σ E).2 hE.1, hE.2⟩
  · intro E hE
    simp only [mem_filter, mem_zeroSets] at hE ⊢
    have hE' : (E.map σ.symm.toEmbedding).map σ.toEmbedding = E := by
      ext x; simp
    have h1 := hE.1
    rw [← hE'] at h1
    rw [hE']
    exact ⟨(isZeroSet_map_equiv u σ _).1 h1, hE.2⟩
  · intro E _
    ext x; simp
  · intro E _
    ext x; simp

/-- `HasIncidenceIdentity` is invariant under reindexing the positions by an equivalence. -/
theorem hasIncidenceIdentity_comp_equiv {R : Type*} [CommRing R] {ι ι' : Type*} [Fintype ι]
    [Fintype ι'] (u : ι → G) (σ : ι' ≃ ι) {t : ℕ} (h : HasIncidenceIdentity R u t) :
    HasIncidenceIdentity R (fun i => u (σ i)) t := by
  classical
  obtain ⟨c, hsum, hJ⟩ := h
  refine ⟨fun E => c (E.map σ.toEmbedding), ?_, ?_⟩
  · have := sum_zeroSets_map_equiv u σ (fun _ => True) c
    simp only [filter_true] at this
    rw [this, hsum]
  · intro J h1 h2
    have := sum_zeroSets_map_equiv u σ (fun E => J.map σ.toEmbedding ⊆ E) c
    simp only [map_subset_map] at this
    convert this.trans (hJ (J.map σ.toEmbedding) (by simpa using h1) (by simpa using h2))

/-! ## Short-zero-freeness along embeddings -/

/-- Short-zero-freeness passes to a reindexed subsequence along an embedding `f : ι' ↪ ι`. -/
theorem isShortZeroFree_comp_embedding {ι ι' : Type*} {u : ι → G} (hu : IsShortZeroFree u)
    (f : ι' ↪ ι) : IsShortZeroFree (fun i => u (f i)) := by
  intro E hE
  have hE' : IsZeroSet u (E.map f) := ⟨hE.1.map, by rw [sum_map]; exact hE.2⟩
  simpa using hu _ hE'

end DavenportProject
