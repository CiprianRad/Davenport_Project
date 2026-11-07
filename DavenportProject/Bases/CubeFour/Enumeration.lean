/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Bases.CubeFour.Codes

/-!
# Completeness of the enumeration for Lemma 5.3

Every sorted short-zero-free list of codes `F` satisfying the normalization guards is reached by
the enumeration `DavenportCompute.gdfs`, so a property `leaf` checked at all of its leaves holds
for `F.reverse`.

* `gdfs_complete`: if `gdfs` accepts from the prefix `acc`, then `leaf (L.reverse ++ acc)` for
  every sorted list `L` of the right length whose entries are never skipped along the way.
* `skip_take_eq_false`: in a sorted list `F` with `ListSZF F` and `Guards F`, the entry `F[k]` is
  not skipped after the prefix `F.take k`. A skip by a sum would give a sublist of `F` of length
  at most four with code sum zero; a skip by a guard contradicts `Guards F` and the order of `F`.
* `leaf_of_prefixes`: if the enumeration split at depth `d` (first up to the prefixes of depth
  `d`, then from each prefix) accepts, then `leaf F.reverse`.
-/

public section

namespace DavenportProject.CubeFour

open DavenportCompute

theorem one_le_of_P1 {x : ℕ} (h : P1 x = true) : 1 ≤ x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [P1] at h
  · exact hx

theorem four_le_of_P2 {x : ℕ} (h : P2 x = true) : 4 ≤ x := by
  by_contra hx
  simp only [P2, Bool.or_eq_true, beq_iff_eq] at h
  omega

theorem sixteen_le_of_P3 {x : ℕ} (h : P3 x = true) : 16 ≤ x := by
  by_contra hx
  simp only [P3, beq_iff_eq] at h
  omega

/-- In a sorted list, the entry at position `k` is at most every entry from position `k` on. -/
theorem getElem_le_of_mem_drop {F : List ℕ} (hsort : F.Pairwise (· ≤ ·)) {k : ℕ}
    (hk : k < F.length) {y : ℕ} (hy : y ∈ F.drop k) : F[k] ≤ y := by
  have hs := hsort.sublist (List.drop_sublist k F)
  rw [List.drop_eq_getElem_cons hk] at hs hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact Nat.le_refl _
  · exact (List.pairwise_cons.1 hs).1 y hy

/-- A guard cannot skip an entry of a sorted list satisfying the corresponding guard of
`Guards`. -/
theorem guard_aux {F : List ℕ} (hsort : F.Pairwise (· ≤ ·)) {k : ℕ} (hk : k < F.length)
    {c : ℕ} {P : ℕ → Bool} (hP : ∀ y, P y = true → c ≤ y) (hg : c ∈ F ∨ ∀ y ∈ F, P y = false)
    (hPx : P F[k] = true) (hne : F[k] ≠ c) (hc : c ∉ F.take k) : False := by
  rcases hg with hcF | hall
  · rw [← List.take_append_drop k F, List.mem_append] at hcF
    have h₁ := getElem_le_of_mem_drop hsort hk (hcF.resolve_left hc)
    have h₂ := hP _ hPx
    omega
  · rw [hall _ (List.getElem_mem hk)] at hPx
    exact Bool.false_ne_true hPx

/-- In a sorted short-zero-free list satisfying the guards, the entry `F[k]` is not skipped
after the prefix `F.take k`. -/
theorem skip_take_eq_false {F : List ℕ} (hsort : F.Pairwise (· ≤ ·))
    (hlt : ∀ y ∈ F, 1 ≤ y ∧ y < 64) (hszf : ListSZF F) (hg : Guards F) {k : ℕ}
    (hk : k < F.length) :
    skip (R1 (F.take k).reverse) (R2 (F.take k).reverse) (R3 (F.take k).reverse) F[k] =
      false := by
  have ha : ∀ y ∈ (F.take k).reverse, y < 64 := fun y hy =>
    (hlt y (List.mem_of_mem_take (List.mem_reverse.1 hy))).2
  have hsub : (F.take k ++ [F[k]]).Sublist F := by
    have h : F.take (k + 1) = F.take k ++ [F[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]
      rfl
    rw [← h]
    exact List.take_sublist _ _
  have hzero : ∀ q : List ℕ, q.Sublist (F.take k).reverse → q.length ≤ 3 →
      codeSum q = neg4 F[k] → False := by
    intro q hq hl hs
    refine hszf (q.reverse ++ [F[k]]) ?_ (by simp) (by simp; omega) ?_
    · exact ((List.reverse_sublist.2 hq).append_right _).trans
        (by simpa using hsub)
    · rw [codeSum_perm ((List.perm_append_singleton _ _).trans ((List.reverse_perm q).cons _)),
        codeSum, hs, add4_neg4]
  have hnot : ∀ c, c < 64 → mem (R1 (F.take k).reverse) c = false → c ∉ F.take k :=
    fun c hc h hmem => by
      rw [← List.mem_reverse, ← mem_R1_iff ha hc, h] at hmem
      exact Bool.false_ne_true hmem
  rw [Bool.eq_false_iff]
  intro h
  simp only [skip, mem_or, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at h
  rcases h with ((((h | h) | h) | ⟨⟨hP, hne⟩, hm⟩) | ⟨⟨hP, hne⟩, hm⟩) | ⟨⟨hP, hne⟩, hm⟩
  · obtain ⟨q, hq, hl, hs⟩ := exists_sublist_of_mem_R1 ha (neg4_lt _) h
    exact hzero q hq (by omega) hs
  · obtain ⟨q, hq, hl, hs⟩ := exists_sublist_of_mem_R2 ha (neg4_lt _) h
    exact hzero q hq (by omega) hs
  · obtain ⟨q, hq, hl, hs⟩ := exists_sublist_of_mem_R3 ha (neg4_lt _) h
    exact hzero q hq (by omega) hs
  · exact guard_aux hsort hk (fun _ => one_le_of_P1) hg.1 hP hne (hnot 1 (by decide) hm)
  · exact guard_aux hsort hk (fun _ => four_le_of_P2) hg.2.1 hP hne (hnot 4 (by decide) hm)
  · exact guard_aux hsort hk (fun _ => sixteen_le_of_P3) hg.2.2 hP hne (hnot 16 (by decide) hm)

/-- Completeness of `gdfs` from the prefix `acc`: if the enumeration accepts, then `leaf` holds
on `L.reverse ++ acc` for every sorted list `L` of entries in `[lo, 64)` of the right length
none of whose entries is skipped after its predecessors. -/
theorem gdfs_complete (leaf : List ℕ → Bool) :
    ∀ (L : List ℕ) (lo : ℕ) (acc : List ℕ), L.Pairwise (· ≤ ·) →
      (∀ y ∈ L, lo ≤ y ∧ y < 64) →
      (∀ k (hk : k < L.length), skip (R1 ((L.take k).reverse ++ acc))
        (R2 ((L.take k).reverse ++ acc)) (R3 ((L.take k).reverse ++ acc)) L[k] = false) →
      gdfs leaf L.length lo acc (R1 acc) (R2 acc) (R3 acc) = true →
      leaf (L.reverse ++ acc) = true
  | [], _, _, _, _, _, h => h
  | x :: L, lo, acc, hs, hb, hns, h => by
    rw [List.length_cons, gdfs, allFrom_eq_true_iff] at h
    have hx := hb x List.mem_cons_self
    have h₁ := h x hx.1 (by omega)
    have h₀ := hns 0 (by simp)
    simp only [List.take_zero, List.reverse_nil, List.nil_append, List.getElem_cons_zero] at h₀
    rw [h₀, Bool.false_or] at h₁
    rw [List.pairwise_cons] at hs
    have := gdfs_complete leaf L x (x :: acc) hs.2
      (fun y hy => ⟨hs.1 y hy, (hb y (List.mem_cons_of_mem _ hy)).2⟩)
      (fun k hk => by
        have h₂ := hns (k + 1) (by simp; omega)
        rw [List.getElem_cons_succ] at h₂
        simpa using h₂) h₁
    simpa using this

/-- Completeness of the enumeration split at depth `d`: the prefixes of depth `d` reached by
`gdfs` are listed by `prefixes d`, and the enumeration continues from each of them. -/
theorem leaf_of_prefixes (leaf : List ℕ → Bool) (d : ℕ) (F : List ℕ) (hd : d ≤ F.length)
    (hsort : F.Pairwise (· ≤ ·)) (hlt : ∀ y ∈ F, 1 ≤ y ∧ y < 64) (hszf : ListSZF F)
    (hg : Guards F)
    (htop : gdfs (fun acc => (prefixes d).contains acc) d 1 [] 0 0 0 = true)
    (hchunks : ∀ p ∈ prefixes d, gdfsFrom leaf (F.length - d) p = true) :
    leaf F.reverse = true := by
  have hlen : (F.take d).length = d := List.length_take_of_le hd
  have h₁ := gdfs_complete (fun acc => (prefixes d).contains acc) (F.take d) 1 []
    (hsort.sublist (List.take_sublist d F)) (fun y hy => hlt y (List.mem_of_mem_take hy))
    (fun k hk => by
      rw [hlen] at hk
      have h := skip_take_eq_false hsort hlt hszf hg (k := k) (by omega)
      rw [List.take_take, Nat.min_eq_left hk.le, List.append_nil, List.getElem_take]
      exact h)
    (by rw [hlen]; exact htop)
  rw [List.append_nil, List.contains_iff_mem] at h₁
  have h₂ := hchunks _ h₁
  unfold gdfsFrom at h₂
  have h₃ := gdfs_complete leaf (F.drop d) ((F.take d).reverse.headD 1) (F.take d).reverse
    (hsort.sublist (List.drop_sublist d F))
    (fun y hy => by
      refine ⟨?_, (hlt y (List.mem_of_mem_drop hy)).2⟩
      rcases hr : (F.take d).reverse with _ | ⟨z, r⟩
      · exact (hlt y (List.mem_of_mem_drop hy)).1
      · have hz : z ∈ F.take d := by
          rw [← List.mem_reverse, hr]
          exact List.mem_cons_self
        have hs := hsort
        rw [← List.take_append_drop d F, List.pairwise_append] at hs
        exact hs.2.2 z hz y hy)
    (fun k hk => by
      rw [List.length_drop] at hk
      have h := skip_take_eq_false hsort hlt hszf hg (k := d + k) (by omega)
      rw [List.take_add, List.reverse_append] at h
      rw [List.getElem_drop]
      exact h)
    (by rw [List.length_drop]; exact h₂)
  rwa [← List.reverse_append, List.take_append_drop] at h₃

end DavenportProject.CubeFour
