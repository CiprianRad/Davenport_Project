/-
Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claudiu G. Pop, George C. Rad, George C. Țurcaș
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
import DavenportProject.Identities.Evaluation
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# The augmentation ideal and the multilinear indicator

For a finite abelian `p`-group `H = ⊕ᵢ C_{p^{aᵢ}}` the augmentation ideal of `𝔽_p[H]` satisfies
`I^{M+1} = 0` with `M = ∑ᵢ (p^{aᵢ} - 1)` (`augIdeal_pow_eq_bot`). This gives the multilinear
indicator polynomial of Lemma 3.1 (`exists_multilinear_indicator`), stated in
`DavenportProject.Transfer.Indicator`.
-/
public section

namespace DavenportProject.Transfer

open Finset MvPolynomial

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℕ}

/-!
## Nilpotency of the augmentation ideal of `𝔽_p[H]` for a finite abelian `p`-group `H`

Let `H = ∏ᵢ ZMod (p ^ aᵢ)` and `M = ∑ᵢ (p ^ aᵢ - 1)`. In the group algebra
`𝔽_p[H] = AddMonoidAlgebra (ZMod p) H`, put `Yᵢ = X^{eᵢ} - 1`. Then `Yᵢ ^ p ^ aᵢ = 0`,
every `X^h - 1` lies in the ideal `I = (Y₁, …, Y_r)`, and `I ^ n = 0` for `n > M`. In
particular any product of more than `M` elements of the form `X^h - 1` vanishes.
-/

/-- The generator `Yᵢ = X^{eᵢ} - 1` of the augmentation ideal, where `eᵢ = Pi.single i 1`. -/
noncomputable def augY (p : ℕ) (a : ι → ℕ) (i : ι) :
    AddMonoidAlgebra (ZMod p) ((i : ι) → ZMod (p ^ a i)) :=
  AddMonoidAlgebra.single (Pi.single i 1) 1 - 1

/-- The ideal `(Y₁, …, Y_r)` of `𝔽_p[H]`, which is the augmentation ideal. -/
noncomputable def augIdeal (p : ℕ) (a : ι → ℕ) :
    Ideal (AddMonoidAlgebra (ZMod p) ((i : ι) → ZMod (p ^ a i))) :=
  Ideal.span (Set.range (augY p a))

omit [Fact p.Prime] [Fintype ι] in
theorem augY_mem_augIdeal (i : ι) : augY p a i ∈ augIdeal p a :=
  Ideal.subset_span ⟨i, rfl⟩

instance charP_addMonoidAlgebra :
    CharP (AddMonoidAlgebra (ZMod p) ((i : ι) → ZMod (p ^ a i))) p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) _).injective p

omit [Fintype ι] in
theorem augY_pow_eq_zero (i : ι) : augY p a i ^ (p ^ a i) = 0 := by
  rw [augY, sub_pow_char_pow, AddMonoidAlgebra.single_pow, one_pow, one_pow]
  have h : (p ^ a i) • (Pi.single i (1 : ZMod (p ^ a i)) : (i : ι) → ZMod (p ^ a i)) = 0 := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [h, ← AddMonoidAlgebra.one_def, sub_self]

/-- A product of `augY`'s with more than `M` factors vanishes (pigeonhole). -/
theorem prod_augY_eq_zero {κ : Type*} [Fintype κ] (g : κ → ι)
    (hn : ∑ i, (p ^ a i - 1) < Fintype.card κ) : ∏ k, augY p a (g k) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, p ^ a i ≤ #{k | g k = i} := by
    by_contra h
    push Not at h
    have hcard : Fintype.card κ = ∑ i, #{k | g k = i} :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    have : ∑ i, #{k | g k = i} ≤ ∑ i, (p ^ a i - 1) :=
      sum_le_sum fun i _ => Nat.le_sub_one_of_lt (h i)
    omega
  rw [← prod_filter_mul_prod_filter_not univ (fun k => g k = i)]
  have : ∏ k ∈ {k | g k = i}, augY p a (g k) = augY p a i ^ #{k | g k = i} := by
    rw [← prod_const]
    exact prod_congr rfl fun k hk => by rw [(mem_filter.mp hk).2]
  rw [this, ← Nat.add_sub_cancel' hi, pow_add, augY_pow_eq_zero, zero_mul, zero_mul]

theorem augIdeal_pow_eq_bot {n : ℕ} (hn : ∑ i, (p ^ a i - 1) < n) :
    augIdeal p a ^ n = ⊥ := by
  rw [augIdeal, Ideal.span, Submodule.span_pow, Submodule.span_eq_bot]
  intro x hx
  obtain ⟨f, rfl⟩ := Set.mem_pow.mp hx
  rw [Fin.prod_ofFn]
  choose g hg using fun k => (f k).2
  simp_rw [← hg]
  exact prod_augY_eq_zero g (by simpa using hn)

omit [Fintype ι] in
theorem single_sub_one_mem_augIdeal [Finite ι] (h : (i : ι) → ZMod (p ^ a i)) :
    AddMonoidAlgebra.single h 1 - 1 ∈ augIdeal p a := by
  cases nonempty_fintype ι
  let T : AddSubmonoid ((i : ι) → ZMod (p ^ a i)) :=
    { carrier := {g | AddMonoidAlgebra.single g 1 - 1 ∈ augIdeal p a}
      zero_mem' := by simp [← AddMonoidAlgebra.one_def]
      add_mem' := by
        intro g g' hg hg'
        simp only [Set.mem_ofPred_eq] at hg hg' ⊢
        have : AddMonoidAlgebra.single (g + g') (1 : ZMod p) - 1 =
            AddMonoidAlgebra.single g 1 * (AddMonoidAlgebra.single g' 1 - 1) +
              (AddMonoidAlgebra.single g 1 - 1) := by
          rw [mul_sub, AddMonoidAlgebra.single_mul_single, mul_one, mul_one]
          abel
        rw [this]
        exact add_mem (Ideal.mul_mem_left _ _ hg') hg }
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hdecomp : h = ∑ i, (h i).val • (Pi.single i 1 : (i : ι) → ZMod (p ^ a i)) := by
    funext j
    have : NeZero (p ^ a j) := ⟨pow_ne_zero _ hp⟩
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  have hmem : h ∈ T := by
    rw [hdecomp]
    exact sum_mem fun i _ => nsmul_mem (show Pi.single i 1 ∈ T from augY_mem_augIdeal i) _
  exact hmem

omit [DecidableEq ι] in
/-- Any product of more than `M = ∑ᵢ (p ^ aᵢ - 1)` elements of the form `X^h - 1` in
`𝔽_p[∏ᵢ ZMod (p ^ aᵢ)]` vanishes. -/
theorem prod_single_sub_one_eq_zero {κ : Type*} (s : Finset κ)
    (g : κ → (i : ι) → ZMod (p ^ a i)) (hs : ∑ i, (p ^ a i - 1) < #s) :
    ∏ j ∈ s, (AddMonoidAlgebra.single (g j) (1 : ZMod p) - 1) = 0 := by
  classical
  have hmem : ∏ j ∈ s, (AddMonoidAlgebra.single (g j) (1 : ZMod p) - 1) ∈
      ∏ _j ∈ s, augIdeal p a :=
    Ideal.prod_mem_prod fun j _ => single_sub_one_mem_augIdeal (g j)
  rwa [prod_const, augIdeal_pow_eq_bot hs, Ideal.mem_bot] at hmem

/-!
## Proof of Lemma 3.1

The polynomial is `P = ∑_J β_J ∏_{j ∈ J} X_j`, where `β_J` is the identity coefficient of
`∏_{j ∈ J} (X^{v_j} - 1)` in `𝔽_p[H]`. Evaluating at `𝟙_E` gives the identity coefficient of
`∏_{j ∈ E} X^{v_j} = X^{∑_{j ∈ E} v_j}`, and `β_J = 0` for `#J > M` by nilpotency of the
augmentation ideal.
-/

/-- The multilinear indicator polynomial of Lemma 3.1 (stated in the module
`DavenportProject.Transfer.Indicator`). -/
theorem exists_multilinear_indicator {p : ℕ} [Fact p.Prime] {r : ℕ} {a : Fin r → ℕ} {N : ℕ}
    {v : Fin N → ((i : Fin r) → ZMod (p ^ a i))} :
    ∃ P : MvPolynomial (Fin N) (ZMod p),
      P ∈ MvPolynomial.restrictDegree (Fin N) (ZMod p) 1 ∧
      P.totalDegree ≤ ∑ i, (p ^ a i - 1) ∧
      ∀ E : Finset (Fin N),
        MvPolynomial.eval ((E : Set (Fin N)).indicator 1) P =
          if ∑ j ∈ E, v j = 0 then 1 else 0 := by
  classical
  let Y : Fin N → AddMonoidAlgebra (ZMod p) ((i : Fin r) → ZMod (p ^ a i)) := fun j =>
    AddMonoidAlgebra.single (v j) 1 - 1
  let β : Finset (Fin N) → ZMod p := fun J => (∏ j ∈ J, Y j).coeff 0
  have hβ : ∀ J, ∑ i, (p ^ a i - 1) < #J → β J = 0 := fun J hJ => by
    simp only [β, Y, prod_single_sub_one_eq_zero J v hJ, AddMonoidAlgebra.coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply]
  have hX : ∀ J : Finset (Fin N),
      (∏ j ∈ J, X j : MvPolynomial (Fin N) (ZMod p)) ∈ restrictDegree (Fin N) (ZMod p) 1 := by
    intro J
    have : (∏ j ∈ J, X j : MvPolynomial (Fin N) (ZMod p)) =
        monomial (∑ j ∈ J, Finsupp.single j 1) 1 := by
      rw [monomial_sum_one]
      rfl
    rw [this, mem_restrictDegree]
    intro s hs i
    rw [Finset.mem_singleton.mp (support_monomial_subset hs), Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    split_ifs <;> simp
  refine ⟨∑ J ∈ univ.powerset, C (β J) * ∏ j ∈ J, X j, ?_, ?_, ?_⟩
  · refine sum_mem fun J _ => ?_
    rw [C_mul']
    exact Submodule.smul_mem _ _ (hX J)
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun J _ => ?_)
    by_cases hJ : ∑ i, (p ^ a i - 1) < #J
    · simp [hβ J hJ]
    · rw [C_mul']
      refine (totalDegree_smul_le _ _).trans ?_
      exact (Identities.totalDegree_prod_X_le J).trans (not_lt.mp hJ)
  · intro E
    have hind : ∀ J : Finset (Fin N),
        ∏ j ∈ J, (E : Set (Fin N)).indicator (1 : Fin N → ZMod p) j =
          if J ⊆ E then 1 else 0 := by
      intro J
      simp only [Set.indicator_apply, Finset.mem_coe, Pi.one_apply]
      rw [Finset.prod_boole]
      rfl
    simp only [map_sum, map_mul, eval_C, map_prod, eval_X, hind, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    have hfilter : ({J ∈ univ.powerset | J ⊆ E} : Finset (Finset (Fin N))) = E.powerset := by
      ext J
      simp
    rw [hfilter]
    have hprod : ∑ J ∈ E.powerset, ∏ j ∈ J, Y j =
        AddMonoidAlgebra.single (∑ j ∈ E, v j) (1 : ZMod p) := by
      have := Finset.prod_add Y (fun _ => 1) E
      simp only [prod_const_one, mul_one] at this
      rw [← this]
      simp only [Y, sub_add_cancel, AddMonoidAlgebra.prod_single, prod_const_one]
    have hcoeff : ∑ J ∈ E.powerset, β J = (∑ J ∈ E.powerset, ∏ j ∈ J, Y j).coeff 0 := by
      rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    rw [hcoeff, hprod, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

end DavenportProject.Transfer
