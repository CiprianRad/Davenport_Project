/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Proposition 4.1, Section 4: counting subsets by the blocks they meet

The coefficient `blockSubsetCount m j i` counts the `j`-element subsets of `i`
disjoint blocks of size `m` that meet every block. Partitioning a subset by its set
of met blocks gives the integral triangular factorization used in the paper.
-/

public section

namespace DavenportProject.Sharpness
open Finset

/-- The `j`-subsets of blocks indexed by `α`, each with `m` points, meeting every block. -/
noncomputable def meetingSubsets (α : Type*) [Fintype α] (m j : ℕ) :
    Finset (Finset (α × Fin m)) := by
  classical
  exact univ.filter fun S => S.card = j ∧ ∀ a, ∃ b, (a, b) ∈ S

@[simp] theorem mem_meetingSubsets {α : Type*} [Fintype α] {m j : ℕ}
    {S : Finset (α × Fin m)} :
    S ∈ meetingSubsets α m j ↔ S.card = j ∧ ∀ a, ∃ b, (a, b) ∈ S := by
  classical
  simp [meetingSubsets]

/-- Paper Section 4's integer `a_{j, i}`: choose `j` points and meet all `i` blocks. -/
noncomputable def blockSubsetCount (m j i : ℕ) : ℕ := (meetingSubsets (Fin i) m j).card

/-- Relabeling the blocks preserves the set of admissible subsets. -/
theorem card_meetingSubsets_congr {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (m j : ℕ) :
    (meetingSubsets α m j).card = (meetingSubsets β m j).card := by
  classical
  let f := (e.prodCongr (Equiv.refl (Fin m))).finsetCongr
  have hf : ∀ S, S ∈ meetingSubsets α m j ↔ f S ∈ meetingSubsets β m j := by
    intro S
    simp only [mem_meetingSubsets]
    have hcard : (f S).card = S.card := card_map _
    rw [hcard]
    constructor
    · rintro ⟨hS, hmeet⟩
      refine ⟨hS, fun b => ?_⟩
      obtain ⟨v, hv⟩ := hmeet (e.symm b)
      exact ⟨v, mem_map.2 ⟨(e.symm b, v), hv, by simp⟩⟩
    · rintro ⟨hS, hmeet⟩
      refine ⟨hS, fun a => ?_⟩
      obtain ⟨v, hv⟩ := hmeet (e a)
      obtain ⟨⟨a', v'⟩, hmem, he⟩ := mem_map.1 hv
      have ha : a' = a := e.injective (congrArg Prod.fst he)
      have hb : v' = v := congrArg Prod.snd he
      subst a'; subst v'
      exact ⟨v, hmem⟩
  exact card_nbij f (fun S hS => (hf S).1 hS) f.injective.injOn
    (fun T hT => ⟨f.symm T, (hf _).2 (by simpa using hT), f.apply_symm_apply T⟩)

/-- A block-index type with `i` elements gives the paper's number `a_{j, i}`. -/
theorem card_meetingSubsets (α : Type*) [Fintype α] (m j : ℕ) :
    (meetingSubsets α m j).card = blockSubsetCount m j (Fintype.card α) :=
  card_meetingSubsets_congr (Fintype.equivFin α) m j

/-- Meeting all blocks means that projection to the block labels is surjective. -/
theorem image_fst_eq_univ {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    {S : Finset (α × Fin m)} (h : ∀ a, ∃ b, (a, b) ∈ S) :
    S.image Prod.fst = univ := by
  classical
  apply eq_univ_of_forall
  intro a
  obtain ⟨b, hb⟩ := h a
  exact mem_image.2 ⟨(a, b), hb, rfl⟩

/-- A subset meeting `i` blocks has at least `i` points: `T` is upper triangular. -/
theorem blockSubsetCount_eq_zero_of_lt {m j i : ℕ} (hji : j < i) :
    blockSubsetCount m j i = 0 := by
  classical
  apply card_eq_zero.2
  apply eq_empty_iff_forall_notMem.2
  intro S hS
  obtain ⟨hc, hm⟩ := mem_meetingSubsets.1 hS
  have hle := card_image_le (s := S) (f := Prod.fst)
  rw [image_fst_eq_univ hm, card_univ, Fintype.card_fin, hc] at hle
  omega

/-- A `j`-subset meeting `j` blocks chooses exactly one point in each block.
This is the paper's diagonal count `a_{j, j} = m^j`. -/
theorem blockSubsetCount_diag (m j : ℕ) : blockSubsetCount m j j = m ^ j := by
  classical
  let graph : (Fin j → Fin m) → Finset (Fin j × Fin m) :=
    fun f => univ.map ⟨fun a => (a, f a), fun a b h => congrArg Prod.fst h⟩
  have hcard : (univ : Finset (Fin j → Fin m)).card = m ^ j := by simp
  rw [← hcard]
  symm
  apply card_bij (fun f _ => graph f)
  · intro f _
    rw [mem_meetingSubsets]
    refine ⟨by simp [graph], fun a => ⟨f a, ?_⟩⟩
    exact mem_map.2 ⟨a, mem_univ _, rfl⟩
  · intro f _ g _ hfg
    funext a
    have ha : (a, f a) ∈ graph g := hfg ▸ mem_map.2 ⟨a, mem_univ _, rfl⟩
    obtain ⟨b, _, hb⟩ := mem_map.1 ha
    have hba : b = a := congrArg Prod.fst hb
    have hval : g b = f a := congrArg Prod.snd hb
    simpa [hba] using hval.symm
  · intro S hS
    obtain ⟨hc, hm⟩ := mem_meetingSubsets.1 hS
    choose f hf using hm
    have hinj : Set.InjOn Prod.fst (S : Set (Fin j × Fin m)) := by
      apply card_image_iff.1
      rw [image_fst_eq_univ (fun a => ⟨f a, hf a⟩), card_univ, Fintype.card_fin, hc]
    refine ⟨f, mem_univ _, ?_⟩
    ext ⟨a, b⟩
    constructor
    · intro h
      obtain ⟨c, _, h⟩ := mem_map.1 h
      change (c, f c) = (a, b) at h
      exact h ▸ hf c
    · intro h
      have hab : (a, f a) = (a, b) := hinj (hf a) h rfl
      exact mem_map.2 ⟨a, mem_univ _, hab⟩

/-- Inclusion of the blocks in a specified set of block labels. -/
def blockInclusion {α : Type*} (I : Finset α) (m : ℕ) :
    (I × Fin m) ↪ (α × Fin m) :=
  (Function.Embedding.subtype (· ∈ I)).prodMap (Function.Embedding.refl _)

/-- Fix the set `I` of met blocks. Removing the unused block labels gives exactly
`a_{j,|I|}` subsets; this is the bijection in the paper's double count. -/
theorem card_block_fiber {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α) (m j : ℕ) :
    ((univ.powersetCard j).filter
      (fun S : Finset (α × Fin m) => S.image Prod.fst = I)).card =
        blockSubsetCount m j I.card := by
  classical
  rw [← Fintype.card_coe I, ← card_meetingSubsets I m j]
  symm
  let e := blockInclusion I m
  apply card_bij (fun S _ => S.map e)
  · intro S hS
    obtain ⟨hc, hm⟩ := mem_meetingSubsets.1 hS
    apply mem_filter.2
    refine ⟨mem_powersetCard.2 ⟨subset_univ _, by simpa using hc⟩, ?_⟩
    ext a
    constructor
    · intro ha
      obtain ⟨x, hx, rfl⟩ := mem_image.1 ha
      obtain ⟨⟨b, v⟩, _, rfl⟩ := mem_map.1 hx
      exact b.2
    · intro ha
      obtain ⟨v, hv⟩ := hm ⟨a, ha⟩
      exact mem_image.2 ⟨(a, v), mem_map.2 ⟨(⟨a, ha⟩, v), hv, rfl⟩, rfl⟩
  · intro S _ T _ h
    exact Finset.map_injective e h
  · intro S hS
    obtain ⟨hSj, hSI⟩ := mem_filter.1 hS
    have hcard := (mem_powersetCard.1 hSj).2
    have hrange : ∀ x ∈ S, x ∈ Set.range e := by
      intro x hx
      have hxI : x.1 ∈ I := hSI ▸ mem_image_of_mem Prod.fst hx
      exact ⟨(⟨x.1, hxI⟩, x.2), rfl⟩
    let T := S.preimage e e.injective.injOn
    have hmap : T.map e = S := by
      rw [map_eq_image, image_preimage]
      exact filter_eq_self.2 hrange
    refine ⟨T, mem_meetingSubsets.2 ⟨?_, ?_⟩, hmap⟩
    · have := congrArg Finset.card hmap
      simpa [hcard] using this
    · intro a
      have ha : a.val ∈ S.image Prod.fst := hSI.symm ▸ a.property
      obtain ⟨⟨b, v⟩, hv, hb⟩ := mem_image.1 ha
      change b = a.val at hb
      subst b
      exact ⟨v, mem_preimage.2 hv⟩

/-- **Proposition 4.1, Section 4, the double count.** A `j`-subset of `k`
blocks first chooses the `i` blocks that it meets, then meets each chosen block. -/
theorem choose_mul_eq_sum_blockSubsetCount (m k j : ℕ) :
    (m * k).choose j =
      ∑ i ∈ range (k + 1), k.choose i * blockSubsetCount m j i := by
  classical
  have hpartition := card_eq_sum_card_fiberwise
    (s := (univ : Finset (Fin k × Fin m)).powersetCard j)
    (t := (univ : Finset (Fin k)).powerset)
    (f := fun S => S.image Prod.fst)
    (fun S _ => mem_powerset.2 (subset_univ _))
  simp only [card_powersetCard, card_univ, Fintype.card_prod, Fintype.card_fin] at hpartition
  simp_rw [card_block_fiber] at hpartition
  rw [sum_powerset_apply_card] at hpartition
  simpa [mul_comm, nsmul_eq_mul] using hpartition

end DavenportProject.Sharpness
