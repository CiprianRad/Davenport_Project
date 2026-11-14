/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import DavenportProject.Bases.CubeFour.SearchBits
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Bitwise

/-!
# Completeness of the kernel enumeration of Lemma 5.3

* `Good acc st`: the state `st` describes the sorted prefix `acc`. Its bit sets contain only
  negatives of sums of at most three entries, and its other fields are the last entry, the
  numbers of entries `1`, `4`, `16` and of the last entry, the code sum and the packed entries.
* `good_step`: `step` keeps this description.
* `testBit_cands`: the codes allowed by `cands`.
* `guard_aux`, `rep_aux`: the guards and the multiplicity normalization of a sorted list.
* `path_of_sorted`: a sorted short-zero-free list of codes satisfying the guards and the
  multiplicity normalization is a path of allowed codes from `root`.
* `loop_sound`, `dfs_sound`, `topDfs_sound`, `chunkRun_sound`: what a successful run of the
  enumeration says about the states along such paths.
-/

@[expose] public section

namespace DavenportProject.CubeFour

open DavenportCompute DavenportCompute.Search

/-! ## The states along a prefix -/

/-- The packed form of a list of codes, the last one lowest. -/
def packL (L : List ℕ) : ℕ := L.foldl (fun q x => q * 64 + x) 0

/-- The state after the codes `L`, starting from `st`. -/
def stepsFrom (st : State) (L : List ℕ) : State := L.foldl step st

/-- `st` describes the prefix `acc`. -/
structure Good (acc : List ℕ) (st : State) : Prop where
  lt : ∀ a ∈ acc, a < 64
  le : ∀ a ∈ acc, a ≤ st.lo
  lo : st.lo = acc.getLastD 1
  P_lt : st.P < 2 ^ 128
  F_lt : st.F < 2 ^ 64
  one : ∀ y < 64, st.P.testBit y = true → ∃ a ∈ acc, add4 a y = 0
  two : ∀ y < 64, st.P.testBit (64 + y) = true →
    ∃ q : List ℕ, q.Sublist acc ∧ q.length = 2 ∧ add4 (codeSum q) y = 0
  three : ∀ y < 64, st.F.testBit y = true →
    ∃ q : List ℕ, q.Sublist acc ∧ q ≠ [] ∧ q.length ≤ 3 ∧ add4 (codeSum q) y = 0
  c1 : st.c1 = acc.count 1
  c4 : st.c4 = acc.count 4
  c16 : st.c16 = acc.count 16
  G : st.G = gmask st.c1 st.c4 st.c16
  run : st.run = acc.count st.lo
  s : st.s = codeSum acc
  q : st.q = packL acc

theorem good_root : Good [] root where
  lt := by simp
  le := by simp
  lo := rfl
  P_lt := by decide
  F_lt := by decide
  one := by simp [root]
  two := by simp [root]
  three := by simp [root]
  c1 := rfl
  c4 := rfl
  c16 := rfl
  G := rfl
  run := rfl
  s := rfl
  q := rfl

/-! ### The fields of `step` -/

theorem cond_beq {α : Type*} (x c : ℕ) (a b : α) :
    cond (Nat.beq x c) a b = if x = c then a else b := by
  cases h : Nat.beq x c
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

theorem not_le_of_ble_false {x n : ℕ} (h : Nat.ble x n = false) : ¬ x ≤ n := fun hle => by
  rw [Nat.ble_eq_true_of_le hle] at h; exact Bool.noConfusion h

section StepFields

variable (st : State) (x : ℕ)

theorem step_lo : (step st x).lo = x := by
  simp only [step, force_eq]; cases Nat.ble x 16 <;> rfl

theorem step_P : (step st x).P = st.P ||| ((1 <<< negc x) |||
    ((transl2 st.P (negc x) &&& FULL) <<< 64)) := by
  simp only [step, force_eq]; cases Nat.ble x 16 <;> rfl

theorem step_F : (step st x).F = st.F ||| ((1 <<< negc x) |||
    ((transl2 st.P (negc x) ||| (transl2 st.P (negc x) >>> 64)) &&& FULL)) := by
  simp only [step, force_eq]; cases Nat.ble x 16 <;> rfl

theorem step_c1 : (step st x).c1 = if x = 1 then st.c1 + 1 else st.c1 := by
  simp only [step, force_eq]
  cases hb : Nat.ble x 16
  · have hx : x ≠ 1 := fun e => not_le_of_ble_false hb (by omega)
    simp [hx]
  · simp

theorem step_c4 : (step st x).c4 = if x = 4 then st.c4 + 1 else st.c4 := by
  simp only [step, force_eq]
  cases hb : Nat.ble x 16
  · have hx : x ≠ 4 := fun e => not_le_of_ble_false hb (by omega)
    simp [hx]
  · simp

theorem step_c16 : (step st x).c16 = if x = 16 then st.c16 + 1 else st.c16 := by
  simp only [step, force_eq]
  cases hb : Nat.ble x 16
  · have hx : x ≠ 16 := fun e => not_le_of_ble_false hb (by omega)
    simp [hx]
  · simp

theorem step_G : (step st x).G =
    if x ≤ 16 then gmask (step st x).c1 (step st x).c4 (step st x).c16 else st.G := by
  rw [step_c1, step_c4, step_c16]
  simp only [step, force_eq]
  cases hb : Nat.ble x 16
  · simp [not_le_of_ble_false hb]
  · simp [Nat.le_of_ble_eq_true hb]

theorem step_run : (step st x).run = if x = st.lo then st.run + 1 else 1 := by
  simp only [step, force_eq]
  cases Nat.ble x 16 <;> simp

theorem step_s : (step st x).s = addc st.s x := by
  simp only [step, force_eq]; cases Nat.ble x 16 <;> rfl

theorem step_q : (step st x).q = (st.q <<< 6) ||| x := by
  simp only [step, force_eq]; cases Nat.ble x 16 <;> rfl

end StepFields

/-! ### Bits of the fields of `step` -/

theorem neg4_neg4 : ∀ x < 64, neg4 (neg4 x) = x := by decide +kernel

theorem testBit_MP : ∀ x < 64,
    MP1.testBit x = P1 x ∧ MP2.testBit x = P2 x ∧ MP3.testBit x = P3 x := by
  decide +kernel

theorem testBit_FULL (j : ℕ) : FULL.testBit j = decide (j < 64) := by
  rw [show FULL = 2 ^ 64 - 1 from rfl, Nat.testBit_two_pow_sub_one]

theorem testBit_one_shiftLeft (n j : ℕ) : (1 <<< n).testBit j = decide (n = j) := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

theorem negc_lt {x : ℕ} (hx : x < 64) : negc x < 64 := by
  rw [negc_eq x hx]; exact neg4_lt x

theorem testBit_step_P_low (st : State) {x y : ℕ} (hx : x < 64) (hy : y < 64) :
    (step st x).P.testBit y = (st.P.testBit y || decide (neg4 x = y)) := by
  rw [step_P, Nat.testBit_lor, Nat.testBit_lor, testBit_one_shiftLeft, Nat.testBit_shiftLeft,
    negc_eq x hx]
  have : ¬ y ≥ 64 := by omega
  simp [this]

theorem testBit_step_P_high (st : State) {x y : ℕ} (hx : x < 64) (hy : y < 64) :
    (step st x).P.testBit (64 + y) = (st.P.testBit (64 + y) || st.P.testBit (add4 y x)) := by
  rw [step_P, Nat.testBit_lor, Nat.testBit_lor, testBit_one_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_land, testBit_FULL, Nat.add_sub_cancel_left,
    testBit_transl2_low _ _ (negc_lt hx) hy, negc_eq x hx, neg4_neg4 x hx]
  have h1 : ¬ neg4 x = 64 + y := by have := neg4_lt x; omega
  simp [h1, hy]

theorem testBit_step_F (st : State) {x y : ℕ} (hx : x < 64) (hy : y < 64) :
    (step st x).F.testBit y = (st.F.testBit y || decide (neg4 x = y) || st.P.testBit (add4 y x) ||
      st.P.testBit (64 + add4 y x)) := by
  rw [step_F, Nat.testBit_lor, Nat.testBit_lor, testBit_one_shiftLeft, Nat.testBit_land,
    Nat.testBit_lor, Nat.testBit_shiftRight, testBit_FULL, testBit_transl2_low _ _ (negc_lt hx) hy,
    show 64 + y = 64 + y from rfl, testBit_transl2_high _ _ (negc_lt hx) hy, negc_eq x hx,
    neg4_neg4 x hx]
  simp [hy, Bool.or_assoc]

theorem step_P_lt (st : State) (hP : st.P < 2 ^ 128) {x : ℕ} (hx : x < 64) :
    (step st x).P < 2 ^ 128 := by
  rw [step_P]
  refine Nat.or_lt_two_pow hP (Nat.or_lt_two_pow ?_ ?_)
  · rw [Nat.shiftLeft_eq, one_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by have := negc_lt hx; omega)
  · rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num]
    exact Nat.mul_lt_mul_of_pos_right (Nat.and_lt_two_pow _ (by decide)) (by norm_num)

theorem step_F_lt (st : State) (hF : st.F < 2 ^ 64) {x : ℕ} (hx : x < 64) :
    (step st x).F < 2 ^ 64 := by
  rw [step_F]
  refine Nat.or_lt_two_pow hF (Nat.or_lt_two_pow ?_ (Nat.and_lt_two_pow _ (by decide)))
  rw [Nat.shiftLeft_eq, one_mul]
  exact Nat.pow_lt_pow_right (by norm_num) (negc_lt hx)

/-! ### `step` keeps the description -/

theorem codeSum_lt (q : List ℕ) : codeSum q < 64 := by
  cases q with
  | nil => decide
  | cons x p => exact add4_lt _ _

theorem codeSum_append_singleton (acc : List ℕ) (x : ℕ) :
    codeSum (acc ++ [x]) = add4 (codeSum acc) x := by
  rw [codeSum_perm (List.perm_append_singleton x acc), codeSum, add4_comm]

theorem packL_append_singleton (acc : List ℕ) (x : ℕ) :
    packL (acc ++ [x]) = packL acc * 64 + x := by
  simp [packL, List.foldl_append]

theorem sublist_pair {acc : List ℕ} {a : ℕ} (ha : a ∈ acc) (x : ℕ) :
    [a, x].Sublist (acc ++ [x]) :=
  (List.singleton_sublist.2 ha).append (List.Sublist.refl [x])

theorem good_step {acc : List ℕ} {st : State} (h : Good acc st) {x : ℕ} (hx : x < 64)
    (hlo : st.lo ≤ x) : Good (acc ++ [x]) (step st x) where
  lt a ha := by
    rcases List.mem_append.1 ha with ha | ha
    · exact h.lt a ha
    · simp only [List.mem_singleton] at ha; omega
  le a ha := by
    rw [step_lo]
    rcases List.mem_append.1 ha with ha | ha
    · exact (h.le a ha).trans hlo
    · simp only [List.mem_singleton] at ha; omega
  lo := by rw [step_lo]; simp
  P_lt := step_P_lt st h.P_lt hx
  F_lt := step_F_lt st h.F_lt hx
  one y hy hb := by
    rw [testBit_step_P_low st hx hy, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · obtain ⟨a, ha, hay⟩ := h.one y hy hb
      exact ⟨a, List.mem_append_left _ ha, hay⟩
    · obtain rfl := of_decide_eq_true hb
      exact ⟨x, by simp, add4_neg4 x⟩
  two y hy hb := by
    rw [testBit_step_P_high st hx hy, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · obtain ⟨q, hq, hl, hs⟩ := h.two y hy hb
      exact ⟨q, hq.trans (List.sublist_append_left _ _), hl, hs⟩
    · obtain ⟨a, ha, hay⟩ := h.one _ (add4_lt _ _) hb
      refine ⟨[a, x], sublist_pair ha x, rfl, ?_⟩
      have ha64 := h.lt a ha
      simp only [codeSum, add4_zero hx]
      rw [add4_assoc, add4_comm x y, hay]
  three y hy hb := by
    rw [testBit_step_F st hx hy] at hb
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
    rcases hb with ((hb | hb) | hb) | hb
    · obtain ⟨q, hq, hne, hl, hs⟩ := h.three y hy hb
      exact ⟨q, hq.trans (List.sublist_append_left _ _), hne, hl, hs⟩
    · subst hb
      exact ⟨[x], by simp, by simp, by simp, by rw [codeSum_singleton hx, add4_neg4]⟩
    · obtain ⟨a, ha, hay⟩ := h.one _ (add4_lt _ _) hb
      refine ⟨[a, x], sublist_pair ha x, by simp, by simp, ?_⟩
      simp only [codeSum, add4_zero hx]
      rw [add4_assoc, add4_comm x y, hay]
    · obtain ⟨q, hq, hl, hs⟩ := h.two _ (add4_lt _ _) hb
      refine ⟨q ++ [x], hq.append (List.Sublist.refl [x]), by simp, by simp [hl], ?_⟩
      rw [codeSum_append_singleton, add4_assoc, add4_comm x y, hs]
  c1 := by
    rw [step_c1, h.c1, List.count_append]; by_cases h1 : x = 1 <;> simp [h1]
  c4 := by
    rw [step_c4, h.c4, List.count_append]; by_cases h1 : x = 4 <;> simp [h1]
  c16 := by
    rw [step_c16, h.c16, List.count_append]; by_cases h1 : x = 16 <;> simp [h1]
  G := by
    rw [step_G]
    split_ifs with h16
    · rfl
    · rw [h.G, step_c1, step_c4, step_c16]
      simp [show x ≠ 1 by omega, show x ≠ 4 by omega, show x ≠ 16 by omega]
  run := by
    rw [step_run, step_lo, List.count_append, List.count_singleton]
    simp only [beq_self_eq_true, ↓reduceIte]
    split_ifs with h1
    · rw [h.run, h1]
    · have : List.count x acc = 0 := List.count_eq_zero.2 fun hm => by
        have := h.le x hm; omega
      rw [this]
  s := by
    rw [step_s, h.s, codeSum_append_singleton, addc_eq _ (codeSum_lt _) _ hx]
  q := by
    rw [step_q, h.q, packL_append_singleton, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : x < 2 ^ 6),
      Nat.shiftLeft_eq]

/-! ## The allowed codes -/

theorem getLastD_eq_or_mem (l : List ℕ) (d : ℕ) : l.getLastD d = d ∨ l.getLastD d ∈ l := by
  rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
  · simp
  · right; simp

theorem gmask_lt (c1 c4 c16 : ℕ) : gmask c1 c4 c16 < 2 ^ 64 := by
  have h : ∀ a b c : Bool,
      Nat.lor (cond a G1 0) (Nat.lor (cond b G4 0) (cond c G16 0)) < 2 ^ 64 := by
    decide +kernel
  exact h _ _ _

theorem Good.lo_lt {acc : List ℕ} {st : State} (h : Good acc st) : st.lo < 64 := by
  rw [h.lo]
  rcases getLastD_eq_or_mem acc 1 with he | hm
  · rw [he]; norm_num
  · exact h.lt _ hm

theorem testBit_cands (st : State) (hF : st.F < 2 ^ 64) (hG : st.G < 2 ^ 64) (hlo : st.lo < 64)
    (x : ℕ) : (cands st).testBit x = (decide (x < 64) && !st.F.testBit x && !st.G.testBit x &&
      decide (st.lo ≤ x) && !(decide (x = st.lo) && !okRep st)) := by
  have hbase : ∀ y,
      (Nat.xor FULL (Nat.lor st.F (Nat.lor st.G (Nat.sub (Nat.shiftLeft 1 st.lo) 1)))).testBit y =
        (decide (y < 64) && !st.F.testBit y && !st.G.testBit y && decide (st.lo ≤ y)) := by
    intro y
    have e : Nat.sub (Nat.shiftLeft 1 st.lo) 1 = 2 ^ st.lo - 1 := by
      rw [show Nat.shiftLeft 1 st.lo = 1 <<< st.lo from rfl, Nat.shiftLeft_eq, one_mul]; rfl
    rw [show Nat.xor FULL _ = FULL ^^^ (st.F ||| (st.G ||| (2 ^ st.lo - 1))) by rw [← e]; rfl,
      Nat.testBit_xor, testBit_FULL, Nat.testBit_lor, Nat.testBit_lor, Nat.testBit_two_pow_sub_one]
    by_cases h1 : y < 64
    · by_cases h2 : y < st.lo <;> simp [h1, h2]; omega
    · have hF' : st.F.testBit y = false :=
        Nat.testBit_eq_false_of_lt (hF.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have hG' : st.G.testBit y = false :=
        Nat.testBit_eq_false_of_lt (hG.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have h2 : ¬ y < st.lo := by omega
      simp [h1, h2, hF', hG']
  simp only [cands, force_eq, bitB_eq]
  generalize hB : Nat.xor FULL (Nat.lor st.F (Nat.lor st.G (Nat.sub (Nat.shiftLeft 1 st.lo) 1))) = B
    at hbase
  have hxor : ∀ y, (Nat.xor B (Nat.shiftLeft 1 st.lo)).testBit y =
      (B.testBit y ^^ decide (st.lo = y)) := fun y => by
    rw [show Nat.xor B (Nat.shiftLeft 1 st.lo) = B ^^^ (1 <<< st.lo) from rfl, Nat.testBit_xor,
      testBit_one_shiftLeft]
  rcases Bool.eq_false_or_eq_true (okRep st) with hok | hok
  · -- `okRep st = true`: nothing is removed
    rw [hok]
    simp only [Bool.not_true, Bool.and_false, Bool.cond_false, hbase]
    simp
  · rcases Bool.eq_false_or_eq_true (B.testBit st.lo) with hbl | hbl
    · rw [hok, hbl]
      simp only [Bool.not_false, Bool.and_self, Bool.cond_true, hxor, hbase]
      by_cases hx : x = st.lo
      · subst hx; rw [hbase] at hbl; simpa using hbl
      · simp [hx, Ne.symm hx]
    · rw [hok, hbl]
      simp only [Bool.not_false, Bool.and_true, Bool.cond_false, hbase]
      by_cases hx : x = st.lo
      · subst hx; rw [hbase] at hbl; simpa using hbl
      · simp [hx]

/-- A path of allowed codes from `st`. -/
def Path : State → List ℕ → Prop
  | _, [] => True
  | st, x :: L => (cands st).testBit x = true ∧ Path (step st x) L

theorem stepsFrom_append (st : State) (L L' : List ℕ) :
    stepsFrom st (L ++ L') = stepsFrom (stepsFrom st L) L' := by
  simp [stepsFrom, List.foldl_append]

theorem path_append {st : State} {L : List ℕ} {x : ℕ} :
    Path st (L ++ [x]) ↔ Path st L ∧ (cands (stepsFrom st L)).testBit x = true := by
  induction L generalizing st with
  | nil => simp [Path, stepsFrom]
  | cons y L ih =>
    simp only [List.cons_append, Path, ih, stepsFrom, List.foldl_cons]
    tauto

theorem path_append' {st : State} {L L' : List ℕ} :
    Path st (L ++ L') ↔ Path st L ∧ Path (stepsFrom st L) L' := by
  induction L generalizing st with
  | nil => simp [Path, stepsFrom]
  | cons y L ih =>
    simp only [List.cons_append, Path, ih, stepsFrom, List.foldl_cons]
    tauto

theorem good_stepsFrom {acc : List ℕ} {st : State} (h : Good acc st) {L : List ℕ} (hL : Path st L) :
    Good (acc ++ L) (stepsFrom st L) := by
  induction L generalizing acc st with
  | nil => simpa [stepsFrom] using h
  | cons x L ih =>
    obtain ⟨hx, hL⟩ := hL
    rw [testBit_cands st h.F_lt (h.G ▸ gmask_lt _ _ _) h.lo_lt] at hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    have := ih (good_step h hx.1.1.1.1 hx.1.2) hL
    simpa [stepsFrom] using this

/-! ## Every normalized sequence is a path -/

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

/-- An entry of a sorted list with property `P` is a basis code `c` or comes after it, if `c`
occurs in the list or no entry has `P`. -/
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

/-- Entries before position `k` of a sorted list are at most its entry at `k`. -/
theorem le_getElem_of_mem_take {F : List ℕ} (hsort : F.Pairwise (· ≤ ·)) {k : ℕ}
    (hk : k < F.length) {a : ℕ} (ha : a ∈ F.take k) : a ≤ F[k] := by
  have hs := hsort
  rw [← List.take_append_drop k F, List.pairwise_append] at hs
  refine hs.2.2 a ha F[k] ?_
  rw [List.mem_drop_iff_getElem]
  exact ⟨0, by simp; omega, by simp⟩

/-- The multiplicity normalization at the next entry `x = F[k]`: if `x` has property `P` and is not
the basis code `c ≤ x`, then one more `x` is still at most as frequent as `c` in `F.take k`. -/
theorem rep_aux {F : List ℕ} (hsort : F.Pairwise (· ≤ ·)) {k : ℕ} (hk : k < F.length) {c : ℕ}
    (hc : c < F[k]) (hcount : F.count F[k] ≤ F.count c) :
    (F.take k).count F[k] + 1 ≤ (F.take k).count c := by
  have h1 : F.count F[k] = (F.take k).count F[k] + (F.drop k).count F[k] := by
    rw [← List.count_append, List.take_append_drop]
  have h2 : 1 ≤ (F.drop k).count F[k] := by
    rw [Nat.one_le_iff_ne_zero, Ne, List.count_eq_zero, not_not, List.mem_drop_iff_getElem]
    exact ⟨0, by simp; omega, by simp⟩
  have h3 : F.count c = (F.take k).count c := by
    rw [← List.take_append_drop k F, List.count_append, List.take_append_drop]
    suffices (F.drop k).count c = 0 by omega
    rw [List.count_eq_zero]
    intro hm
    have := getElem_le_of_mem_drop hsort hk hm
    omega
  omega

theorem cands_next {F : List ℕ} (hsort : F.Pairwise (· ≤ ·)) (hlt : ∀ y ∈ F, 1 ≤ y ∧ y < 64)
    (hszf : ListSZF F) (hg : Guards F) (hn3 : n3cond F.reverse = true) {k : ℕ} (hk : k < F.length)
    {st : State} (h : Good (F.take k) st) : (cands st).testBit F[k] = true := by
  have hx := hlt F[k] (List.getElem_mem hk)
  have hsub : (F.take k ++ [F[k]]).Sublist F := by
    rw [← List.take_succ_eq_append_getElem hk]
    exact List.take_sublist _ _
  -- not the negative of a short sum
  have hF : st.F.testBit F[k] = false := by
    rw [Bool.eq_false_iff]
    intro hb
    obtain ⟨q, hq, hne, hl, hs⟩ := h.three _ hx.2 hb
    exact hszf (q ++ [F[k]]) ((hq.append (List.Sublist.refl _)).trans hsub) (by simp)
      (by simp; omega) (by rw [codeSum_append_singleton]; exact hs)
  -- not excluded by a guard
  have hG : st.G.testBit F[k] = false := by
    rw [h.G, testBit_gmask _ _ _ hx.2, h.c1, h.c4, h.c16]
    have g : ∀ (c : ℕ) (P : ℕ → Bool), (∀ y, P y = true → c ≤ y) →
        (c ∈ F ∨ ∀ y ∈ F, P y = false) →
        (decide ((F.take k).count c = 0) && P F[k] && F[k] != c) = false := by
      intro c P hP hgc
      rw [Bool.eq_false_iff]
      intro hb
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hb
      exact guard_aux hsort hk hP hgc hb.1.2 hb.2 (List.count_eq_zero.1 hb.1.1)
    rw [g 1 P1 (fun _ => one_le_of_P1) hg.1, g 4 P2 (fun _ => four_le_of_P2) hg.2.1,
      g 16 P3 (fun _ => sixteen_le_of_P3) hg.2.2]
    rfl
  -- at least the last code
  have hlo : st.lo ≤ F[k] := by
    rw [h.lo]
    rcases getLastD_eq_or_mem (F.take k) 1 with he | hm
    · rw [he]; exact hx.1
    · exact le_getElem_of_mem_take hsort hk hm
  -- the multiplicity normalization
  have hrep : (decide (F[k] = st.lo) && !okRep st) = false := by
    by_cases he : F[k] = st.lo
    · have hcnt : ∀ y ∈ F, (P1 y = true → F.count y ≤ F.count 1) ∧
          (P2 y = true → F.count y ≤ F.count 4) ∧ (P3 y = true → F.count y ≤ F.count 16) := by
        intro y hy
        have := List.all_eq_true.1 hn3 y (List.mem_reverse.2 hy)
        simp only [List.count_reverse, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
          decide_eq_true_eq] at this
        refine ⟨fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
        · rcases this.1.1 with h | h
          · simp [h] at h1
          · exact h
        · rcases this.1.2 with h | h
          · simp [h] at h2
          · exact h
        · rcases this.2 with h | h
          · simp [h] at h3
          · exact h
      obtain ⟨c1, c4, c16⟩ := hcnt F[k] (List.getElem_mem hk)
      obtain ⟨m1, m2, m3⟩ := testBit_MP F[k] hx.2
      have hrun : st.run = (F.take k).count F[k] := by rw [h.run, he]
      have ok : okRep st = true := by
        simp only [okRep, bitB_eq, ← he, m1, m2, m3, hrun]
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq, Nat.ble_eq]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · by_cases hp : P1 F[k] = true
          · by_cases h1 : F[k] = 1
            · exact Or.inl (Or.inr h1)
            · right
              have := rep_aux hsort hk (by have := one_le_of_P1 hp; omega) (c1 hp)
              rw [h.c1]; omega
          · exact Or.inl (Or.inl (by simpa using hp))
        · by_cases hp : P2 F[k] = true
          · by_cases h1 : F[k] = 4
            · exact Or.inl (Or.inr h1)
            · right
              have := rep_aux hsort hk (by have := four_le_of_P2 hp; omega) (c4 hp)
              rw [h.c4]; omega
          · exact Or.inl (Or.inl (by simpa using hp))
        · by_cases hp : P3 F[k] = true
          · by_cases h1 : F[k] = 16
            · exact Or.inl (Or.inr h1)
            · right
              have := rep_aux hsort hk (by have := sixteen_le_of_P3 hp; omega) (c16 hp)
              rw [h.c16]; omega
          · exact Or.inl (Or.inl (by simpa using hp))
      simp [ok]
    · simp [he]
  rw [testBit_cands st h.F_lt (h.G ▸ gmask_lt _ _ _) h.lo_lt, hF, hG, hrep]
  simp [hx.2, hlo]

/-- A sorted list of codes in `[1, 64)` that is short-zero-free and satisfies the guards and the
multiplicity normalization is a path of allowed codes from `root`. -/
theorem path_of_sorted {F : List ℕ} (hsort : F.Pairwise (· ≤ ·)) (hlt : ∀ y ∈ F, 1 ≤ y ∧ y < 64)
    (hszf : ListSZF F) (hg : Guards F) (hn3 : n3cond F.reverse = true) : Path root F := by
  suffices h : ∀ k ≤ F.length, Path root (F.take k) by
    simpa using h F.length le_rfl
  intro k
  induction k with
  | zero => intro _; simp [Path]
  | succ k ih =>
    intro hk
    have hk' : k < F.length := by omega
    have hP := ih (by omega)
    rw [List.take_succ_eq_append_getElem hk', path_append]
    refine ⟨hP, ?_⟩
    have hgood := good_stepsFrom good_root hP
    rw [List.nil_append] at hgood
    exact cands_next hsort hlt hszf hg hn3 hk' hgood

/-! ## Successful runs of the enumeration -/

theorem loop_sound {α : Type} (f : ℕ → α → Option α) (R : α → α → Prop) (hrefl : ∀ d, R d d)
    (htrans : ∀ a b c, R a b → R b c → R a c) (hf : ∀ x d d', f x d = some d' → R d d') :
    ∀ (fuel cand : ℕ) (d d' : α), loop f fuel cand d = some d' →
      R d d' ∧ ∀ x, cand.testBit x = true → ∃ d₁ d₂, R d d₁ ∧ f x d₁ = some d₂ := by
  intro fuel
  induction fuel with
  | zero =>
    intro cand d d' h
    change cond (Nat.beq cand 0) (some d) none = some d' at h
    cases hc : Nat.beq cand 0
    · rw [hc] at h; simp at h
    · rw [hc] at h
      have hc0 : cand = 0 := Nat.eq_of_beq_eq_true hc
      subst hc0
      simp only [Bool.cond_true, Option.some.injEq] at h
      subst h
      exact ⟨hrefl d, fun x hx => by simp at hx⟩
  | succ n ih =>
    intro cand d d' h
    change cond (Nat.beq cand 0) (some d) (force (lowIdx cand) fun z =>
      (f z d).bind (loop f n (Nat.xor cand (Nat.shiftLeft 1 z)))) = some d' at h
    cases hc : Nat.beq cand 0
    · rw [hc, Bool.cond_false, force_eq] at h
      cases hfz : f (lowIdx cand) d with
      | none => rw [hfz] at h; simp at h
      | some d₁ =>
        rw [hfz, Option.bind_some] at h
        obtain ⟨hR, hrest⟩ := ih _ _ _ h
        have hd₁ := hf _ _ _ hfz
        refine ⟨htrans _ _ _ hd₁ hR, fun x hx => ?_⟩
        by_cases hxz : x = lowIdx cand
        · exact ⟨d, d₁, hrefl d, hxz ▸ hfz⟩
        · have hx' : (Nat.xor cand (Nat.shiftLeft 1 (lowIdx cand))).testBit x = true := by
            rw [show Nat.xor cand (Nat.shiftLeft 1 (lowIdx cand)) = cand ^^^ (1 <<< lowIdx cand)
              from rfl, Nat.testBit_xor, testBit_one_shiftLeft, hx]
            simp [Ne.symm hxz]
          obtain ⟨d₂, d₃, hR₂, hf₂⟩ := hrest x hx'
          exact ⟨d₂, d₃, htrans _ _ _ hd₁ hR₂, hf₂⟩
    · have hc0 : cand = 0 := Nat.eq_of_beq_eq_true hc
      subst hc0
      rw [hc, Bool.cond_true] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hrefl d, fun x hx => by simp at hx⟩

theorem dfs_sound {α : Type} (mid leaf : State → α → Option α) (k : ℕ) :
    ∀ (n : ℕ) (st : State) (d d' : α), dfs mid leaf k n st d = some d' →
      ∀ L : List ℕ, Path st L → L.length ≤ n →
        (L.length = n → ∃ d₁ d₂, leaf (stepsFrom st L) d₁ = some d₂) ∧
        (n = L.length + k + 1 → ∃ d₁ d₂, mid (stepsFrom st L) d₁ = some d₂) := by
  intro n
  induction n with
  | zero =>
    intro st d d' h L hL hlen
    have hL0 : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hL0
    exact ⟨fun _ => ⟨d, d', h⟩, fun h' => by simp at h'⟩
  | succ m ih =>
    intro st d d' h L hL hlen
    change cond (Nat.beq m k)
      ((mid st d).bind (loop (fun x => dfs mid leaf k m (step st x)) 64 (cands st)))
      (loop (fun x => dfs mid leaf k m (step st x)) 64 (cands st) d) = some d' at h
    have key : (∃ d₀, loop (fun x => dfs mid leaf k m (step st x)) 64 (cands st) d₀ = some d') ∧
        (m = k → ∃ d₁ d₂, mid st d₁ = some d₂) := by
      cases hmk : Nat.beq m k
      · rw [hmk, Bool.cond_false] at h
        refine ⟨⟨d, h⟩, fun e => ?_⟩
        subst e
        simp at hmk
      · rw [hmk, Bool.cond_true] at h
        cases hmid : mid st d with
        | none => rw [hmid] at h; simp at h
        | some d₁ =>
          rw [hmid, Option.bind_some] at h
          exact ⟨⟨d₁, h⟩, fun _ => ⟨d, d₁, hmid⟩⟩
    obtain ⟨⟨d₀, hloop⟩, hmid⟩ := key
    cases L with
    | nil =>
      refine ⟨fun h' => by simp at h', fun h' => ?_⟩
      simp only [List.length_nil, zero_add] at h'
      exact hmid (by omega)
    | cons x L =>
      obtain ⟨hx, hL⟩ := hL
      obtain ⟨-, hall⟩ := loop_sound _ (fun _ _ => True) (fun _ => trivial)
        (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) 64 _ d₀ d' hloop
      obtain ⟨d₁, d₂, -, hd⟩ := hall x hx
      have := ih (step st x) d₁ d₂ hd L hL (by simp at hlen; omega)
      simp only [List.length_cons] at *
      exact ⟨fun h' => this.1 (by omega), fun h' => this.2 (by omega)⟩

theorem topDfs_suffix : ∀ (n : ℕ) (st : State) (ts ts' : List ℕ), topDfs n st ts = some ts' →
    ts' <:+ ts := by
  intro n
  induction n with
  | zero =>
    intro st ts ts' h
    rcases ts with _ | ⟨t, ts⟩
    · exact absurd h (by intro h; cases h)
    · change cond (Nat.beq t (token st 14)) (some ts) none = some ts' at h
      cases hb : Nat.beq t (token st 14)
      · rw [hb, Bool.cond_false] at h; cases h
      · rw [hb, Bool.cond_true] at h; cases h; exact List.suffix_cons _ _
  | succ m ih =>
    intro st ts ts' h
    rcases ts with _ | ⟨t, ts⟩
    · exact absurd h (by intro h; cases h)
    · change cond (Nat.beq t 0) (loop (fun x => topDfs m (step st x)) 64 (cands st) ts)
          (cond (Nat.beq t (token st (Nat.sub 13 m))) (some ts) none) = some ts' at h
      cases hb : Nat.beq t 0
      · rw [hb, Bool.cond_false] at h
        cases hb' : Nat.beq t (token st (Nat.sub 13 m))
        · rw [hb', Bool.cond_false] at h; cases h
        · rw [hb', Bool.cond_true] at h; cases h; exact List.suffix_cons _ _
      · rw [hb, Bool.cond_true] at h
        have := (loop_sound _ (fun a b => b <:+ a) (fun d => List.suffix_refl d)
          (fun a b c h₁ h₂ => h₂.trans h₁) (fun x d d' h => ih _ _ _ h) 64 _ _ _ h).1
        exact this.trans (List.suffix_cons _ _)

theorem token_ne_zero_of_depth (st : State) {k : ℕ} (hk : 0 < k) : token st k ≠ 0 := by
  change 16 * st.q + k ≠ 0
  omega

theorem topDfs_sound : ∀ (n : ℕ), n ≤ 14 → ∀ (st : State) (ts ts' : List ℕ),
    topDfs n st ts = some ts' → ∀ L : List ℕ, Path st L → n ≤ L.length →
      ∃ j ≤ n, token (stepsFrom st (L.take j)) (14 - n + j) ∈ ts ∧
        token (stepsFrom st (L.take j)) (14 - n + j) ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro _ st ts ts' h L _ _
    rcases ts with _ | ⟨t, ts⟩
    · exact absurd h (by intro h; cases h)
    · change cond (Nat.beq t (token st 14)) (some ts) none = some ts' at h
      cases hb : Nat.beq t (token st 14)
      · rw [hb, Bool.cond_false] at h; cases h
      have ht : t = token st 14 := Nat.eq_of_beq_eq_true hb
      have e : token (stepsFrom st (L.take 0)) (14 - 0 + 0) = t := by rw [List.take_zero, ht]; rfl
      exact ⟨0, le_rfl, e ▸ List.mem_cons_self, e ▸ ht ▸ token_ne_zero_of_depth _ (by norm_num)⟩
  | succ m ih =>
    intro hm st ts ts' h L hL hlen
    rcases ts with _ | ⟨t, ts⟩
    · exact absurd h (by intro h; cases h)
    · change cond (Nat.beq t 0) (loop (fun x => topDfs m (step st x)) 64 (cands st) ts)
          (cond (Nat.beq t (token st (Nat.sub 13 m))) (some ts) none) = some ts' at h
      cases hb : Nat.beq t 0
      · rw [hb, Bool.cond_false] at h
        cases hb' : Nat.beq t (token st (Nat.sub 13 m))
        · rw [hb', Bool.cond_false] at h; cases h
        have ht : t = token st (Nat.sub 13 m) := Nat.eq_of_beq_eq_true hb'
        have ht0 : t ≠ 0 := fun e => by simp [e] at hb
        have e : token (stepsFrom st (L.take 0)) (14 - (m + 1) + 0) = t := by
          rw [List.take_zero, ht]
          change token st _ = token st (13 - m)
          congr 1
          omega
        exact ⟨0, Nat.zero_le _, e ▸ List.mem_cons_self, e ▸ ht0⟩
      · rw [hb, Bool.cond_true] at h
        rcases L with _ | ⟨x, L⟩
        · simp at hlen
        · obtain ⟨hx, hL⟩ := hL
          obtain ⟨-, hall⟩ := loop_sound _ (fun a b => b <:+ a) (fun d => List.suffix_refl d)
            (fun a b c h₁ h₂ => h₂.trans h₁) (fun x d d' h => topDfs_suffix _ _ _ _ h) 64 _ _ _ h
          obtain ⟨d₁, d₂, hsuf, hd⟩ := hall x hx
          obtain ⟨j, hj, hmem, hne⟩ := ih (by omega) _ _ _ hd L hL (by simp at hlen; omega)
          refine ⟨j + 1, by omega, ?_, ?_⟩
          · have e : 14 - (m + 1) + (j + 1) = 14 - m + j := by omega
            rw [e]
            exact List.mem_cons_of_mem _ (hsuf.subset hmem)
          · have e : 14 - (m + 1) + (j + 1) = 14 - m + j := by omega
            rw [e]
            exact hne

theorem foldl_bind_none {α β : Type} (g : β → α → Option α) (ts : List β) :
    ts.foldl (fun acc t => acc.bind (g t)) none = none := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact ih

theorem foldl_bind_sound {α β : Type} (g : β → α → Option α) :
    ∀ (ts : List β) (a : Option α) (d' : α), ts.foldl (fun acc t => acc.bind (g t)) a = some d' →
      ∀ t ∈ ts, ∃ d₁ d₂, g t d₁ = some d₂ := by
  intro ts
  induction ts with
  | nil => intro _ _ _ t ht; simp at ht
  | cons t ts ih =>
    intro a d' h u hu
    simp only [List.foldl_cons] at h
    rcases a with _ | a
    · rw [Option.bind_none, foldl_bind_none] at h; simp at h
    · cases hg : g t a with
      | none => rw [Option.bind_some, hg, foldl_bind_none] at h; simp at h
      | some b =>
        rw [Option.bind_some, hg] at h
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨a, b, hg⟩
        · exact ih _ _ h u hu

theorem chunkRun_sound {ts : List ℕ} {d d' : ℕ} (h : chunkRun ts d = some d') :
    ∀ t ∈ ts, ∃ d₁ d₂, dfs (leaf 14 1) (leaf 18 2) 3 (Nat.sub 18 (Nat.land t 15))
      ((prefixOf t).foldl step root) d₁ = some d₂ :=
  foldl_bind_sound _ ts _ d' h

/-! ## Decoding chunk roots -/

theorem codesOf_packL : ∀ L : List ℕ, (∀ a ∈ L, a < 64) → codesOf L.length (packL L) = L := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton L x ih =>
    intro hL
    have hx : x < 64 := hL x (by simp)
    rw [List.length_append, List.length_singleton, packL_append_singleton]
    change codesOf L.length (Nat.shiftRight (packL L * 64 + x) 6) ++
      [Nat.land (packL L * 64 + x) 63] = _
    have e1 : Nat.shiftRight (packL L * 64 + x) 6 = packL L := by
      rw [show Nat.shiftRight (packL L * 64 + x) 6 = (packL L * 64 + x) >>> 6 from rfl,
        Nat.shiftRight_eq_div_pow]
      omega
    have e2 : Nat.land (packL L * 64 + x) 63 = x := by
      rw [show Nat.land (packL L * 64 + x) 63 = (packL L * 64 + x) &&& (2 ^ 6 - 1) from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
      omega
    rw [e1, e2, ih fun a ha => hL a (by simp [ha])]

theorem prefixOf_token (L : List ℕ) (hL : ∀ a ∈ L, a < 64) (hlen : L.length < 16) :
    prefixOf (16 * packL L + L.length) = L := by
  have e1 : Nat.land (16 * packL L + L.length) 15 = L.length := by
    rw [show Nat.land (16 * packL L + L.length) 15 =
      (16 * packL L + L.length) &&& (2 ^ 4 - 1) from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have e2 : Nat.shiftRight (16 * packL L + L.length) 4 = packL L := by
    rw [show Nat.shiftRight (16 * packL L + L.length) 4 = (16 * packL L + L.length) >>> 4 from rfl,
      Nat.shiftRight_eq_div_pow]
    omega
  rw [prefixOf, e1, e2, codesOf_packL L hL]

/-! ## Every path of length fourteen or eighteen is tested -/

/-- If the enumeration down to the chunk roots succeeds and every chunk root is checked, then the
test at depth fourteen succeeds at every path of length fourteen from `root`, and the test at depth
eighteen at every path of length eighteen. -/
theorem leaf_of_runs {ts : List ℕ} (htop : topDfs 14 root ts = some [])
    (hchunks : ∀ t ∈ ts, t ≠ 0 → ∃ d₁ d₂, dfs (leaf 14 1) (leaf 18 2) 3 (Nat.sub 18 (Nat.land t 15))
      ((prefixOf t).foldl step root) d₁ = some d₂)
    {L : List ℕ} (hL : Path root L) (hlen : L.length = 14 ∨ L.length = 18) :
    (L.length = 14 → ∃ d₁ d₂, leaf 14 1 (stepsFrom root L) d₁ = some d₂) ∧
      (L.length = 18 → ∃ d₁ d₂, leaf 18 2 (stepsFrom root L) d₁ = some d₂) := by
  obtain ⟨j, hj, hmem, hne⟩ := topDfs_sound 14 le_rfl root ts [] htop L hL (by omega)
  have hpath := hL
  rw [← List.take_append_drop j L, path_append'] at hpath
  have hgood := good_stepsFrom good_root hpath.1
  rw [List.nil_append] at hgood
  have hlenj : (L.take j).length = j := List.length_take_of_le (by omega)
  have htok : token (stepsFrom root (L.take j)) (14 - 14 + j) =
      16 * packL (L.take j) + (L.take j).length := by
    rw [hlenj, ← hgood.q, Nat.sub_self, Nat.zero_add]; rfl
  obtain ⟨d₁, d₂, hd⟩ := hchunks _ hmem hne
  rw [htok, prefixOf_token _ hgood.lt (by omega)] at hd
  have e18 : Nat.sub 18 (Nat.land (16 * packL (L.take j) + (L.take j).length) 15) = 18 - j := by
    rw [show Nat.land (16 * packL (L.take j) + (L.take j).length) 15 =
      (16 * packL (L.take j) + (L.take j).length) &&& (2 ^ 4 - 1) from rfl,
      Nat.and_two_pow_sub_one_eq_mod, hlenj]
    change 18 - _ = _
    omega
  rw [e18] at hd
  have hd' : dfs (leaf 14 1) (leaf 18 2) 3 (18 - j) (stepsFrom root (L.take j)) d₁ = some d₂ := hd
  have hs := dfs_sound _ _ 3 (18 - j) _ _ _ hd' (L.drop j) hpath.2 (by simp; omega)
  rw [← stepsFrom_append, List.take_append_drop] at hs
  refine ⟨fun h14 => hs.2 (by simp; omega), fun h18 => hs.1 (by simp; omega)⟩

/-! ## The tests at a leaf -/

theorem packL_div_pow : ∀ (L : List ℕ), (∀ a ∈ L, a < 64) → ∀ (i : ℕ) (hi : i < L.length),
    packL L / 64 ^ (L.length - 1 - i) % 64 = L[i] := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _ i hi; simp at hi
  | append_singleton L x ih =>
    intro hL i hi
    have hx : x < 64 := hL x (by simp)
    rw [packL_append_singleton]
    simp only [List.length_append, List.length_singleton] at hi ⊢
    rcases Nat.lt_or_ge i L.length with h | h
    · have e : L.length + 1 - 1 - i = (L.length - 1 - i) + 1 := by omega
      rw [e, pow_succ', ← Nat.div_div_eq_div_mul, Nat.mul_comm (packL L) 64,
        Nat.mul_add_div (by norm_num : 0 < 64), Nat.div_eq_of_lt hx, Nat.add_zero,
        ih (fun a ha => hL a (by simp [ha])) i h, List.getElem_append_left h]
    · have hi' : i = L.length := by omega
      subst hi'
      simp [Nat.mod_eq_of_lt hx]

theorem neg4_eq_zero : ∀ s < 64, neg4 s = 0 → s = 0 := by decide +kernel

theorem eq_of_add4_neg4 : ∀ a < 64, ∀ s < 64, add4 a (neg4 s) = 0 → a = s := by decide +kernel

/-- `long st` at a leaf: the complement of at most three positions is a zero set. -/
theorem exists_long_zeroSet {N : ℕ} (hN : 4 ≤ N) (c : Fin N → ℕ) {st : State}
    (hgood : Good (List.ofFn c) st) (hlong : long st = true) :
    ∃ Z : Finset (Fin N), IsZeroSet (fun k => dec 4 (c k)) Z ∧ N ≤ Z.card + 3 := by
  classical
  have hs64 : st.s < 64 := hgood.s ▸ codeSum_lt _
  have htot : ∑ k, dec 4 (c k) = dec 4 st.s := by
    rw [hgood.s, dec_codeSum, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [long, bitB_eq, show Nat.lor st.F 1 = st.F ||| 1 from rfl, Nat.testBit_lor,
    negc_eq _ hs64, Bool.or_eq_true] at hlong
  rcases hlong with hF | h0
  · obtain ⟨q, hq, hne, hl, hs⟩ := hgood.three _ (neg4_lt _) hF
    have hqs : codeSum q = st.s := eq_of_add4_neg4 _ (codeSum_lt _) _ hs64 hs
    obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hq
    let e : Fin q.length ↪ Fin N := g.toEmbedding.trans (finCongr List.length_ofFn).toEmbedding
    have he : ∀ i, q.get i = c (e i) := by
      intro i
      rw [hg i]
      simp only [List.get_ofFn]
      rfl
    have hsumq : ∑ k ∈ Finset.univ.map e, dec 4 (c k) = dec 4 st.s := by
      rw [Finset.sum_map, ← hqs, dec_codeSum]
      simp_rw [← he]
      simp
    have hcard : (Finset.univ.map e)ᶜ.card + q.length = N := by
      rw [Finset.card_compl, Finset.card_map, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
      have : q.length ≤ N := by simpa using hq.length_le
      omega
    refine ⟨(Finset.univ.map e)ᶜ, ⟨?_, ?_⟩, by omega⟩
    · rw [← Finset.card_pos]; omega
    · have := Finset.sum_compl_add_sum (Finset.univ.map e) (fun k => dec 4 (c k))
      rw [htot, hsumq] at this
      simpa using this
  · have h1 : ∀ n < 64, Nat.testBit 1 n = true → n = 0 := by decide
    have hs0 : st.s = 0 := neg4_eq_zero _ hs64 (h1 _ (neg4_lt _) h0)
    refine ⟨Finset.univ, ⟨Finset.univ_nonempty_iff.2 ⟨⟨0, by omega⟩⟩, ?_⟩, by simp⟩
    rw [htot, hs0, dec_zero]

end DavenportProject.CubeFour
