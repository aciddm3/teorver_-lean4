-- import Mathlib.Analysis.SeqLimit
  -- пределы последовательностей, limsup, liminf
-- import Mathlib.Algebra.BigOperators.Group.Finset
  -- ∑ s, f, свойства сумм
import Mathlib.Data.Real.Basic
  -- ℝ, ≤, <, |·|, sup, inf, арифметика, exp, log
import Mathlib.Data.Fintype.Basic
  -- конечные типы, Fintype.card
import Mathlib.Data.Finset.Basic
  -- конечные подмножества, Finset.filter, Finset.image
import Mathlib.Order.Heyting.Basic

import Mathlib.Tactic.Linarith
  -- автоматизация линейных неравенств
import Mathlib.Tactic.FieldSimp
  -- упрощение выражений в полях (ℝ)
import Mathlib.Topology.Algebra.InfiniteSum.Basic

import Teorver.SigmaAlgebra

#find "∑' n, ?f n = ?f 0 + ∑' n, ?f (n + 1)"

structure ProbSpace (Ω : Type*) where
  F : SigmaAlgebra Ω
  p : Set Ω → Real                      -- 1. Определяем на всех подмножествах
  p_nonneg : ∀ s ∈ F.sets, 0 ≤ p s      -- 2. Неотрицательность
  p_univ : p Set.univ = 1               -- 3. Нормировка на полном множестве
  p_add : ∀ (f : Nat → Set Ω),          -- 4. σ-аддитивность
    (∀ n, f n ∈ F.sets) ->
    (∀ i j, i ≠ j -> Disjoint (f i) (f j)) ->
    p (⋃ n, f n) = ∑' n, p (f n)
namespace ProbSpace

theorem prob_empty_eq_zero {α : Type*} (P : ProbSpace α) : P.p ∅ = 0 := by
  let empty_seq : Nat -> Set α := fun n ↦ ∅
  have hav1 : P.p (⋃ n, empty_seq n) = ∑' n, P.p (empty_seq n) := by
    have empty_seq_in_f
      : ∀ n, empty_seq n ∈ P.F.sets := by
      simp [empty_seq]
      apply SigmaAlgebra.empty_mem
    have disj
      : ∀ i j, i ≠ j -> Disjoint (empty_seq i) (empty_seq j) := by
      intros i j _
      simp [empty_seq]
    apply P.p_add empty_seq empty_seq_in_f disj
  simp [empty_seq] at hav1
  exact hav1

lemma p_add2 {α : Type*} (P : ProbSpace α) {A B : Set α}
    (hA : A ∈ P.F.sets) (hB : B ∈ P.F.sets) (hD : Disjoint A B)
    : P.p (A ∪ B) = P.p A + P.p B := by
  let seq : ℕ → Set α := fun n =>
      if n = 0 then A
      else if n = 1 then B
      else ∅
  have hav_add : P.p (⋃ n, seq n) = ∑' n, P.p (seq n) := by
      have hav2_1 :  ∀ n, seq n ∈ P.F.sets := by
        intro n
        by_cases h0 : n = 0
        .
          rw[h0]
          simp [seq]
          exact hA
        .
          by_cases h1 : n = 1
          .
            rw[h1]
            simp [seq]
            exact hB
          .
            simp [seq, h0, h1]
            exact SigmaAlgebra.empty_mem P.F
      have hav2_2
        : ∀ i j, i ≠ j → Disjoint (seq i) (seq j) := by
          intro n1 n2 h
          rcases n1 with _|_|_
          · rcases n2 with _|_|_
            . contradiction
            . simp [seq]
              apply hD
            . simp [seq, Disjoint]
          · rcases n2 with _|_|_
            . simp [seq]
              apply hD.symm
            . contradiction
            . simp [seq, Disjoint]
          · rcases n2 with _|_|_
            . simp [seq]
            . simp [seq]
            . simp [seq, Disjoint]
      exact P.p_add seq hav2_1 hav2_2
  simp at hav_add
  have h_sum_split : ∑' n, P.p (seq n) = P.p (seq 0) + P.p (seq 1) + ∑' n, P.p (seq (n+2)) := by
    rw [tsum_eq_sum (s := Finset.range 2)]
    simp [Finset.sum_range_succ]
    simp [seq]
    intro h
    simp [seq]
    intro h2
    cases h with
    | zero => contradiction          -- 1 < 0 → противоречие
    | succ h' => cases h' with
      | zero => contradiction        -- 1 < 1 → противоречие
      | succ _ => simp [prob_empty_eq_zero P]
  rw [<- hav_add] at h_sum_split
  rw [<- Set.union_iUnion_nat_succ seq] at h_sum_split
  rw [<- Set.union_iUnion_nat_succ fun n => seq (n+1)] at h_sum_split
  simp [seq] at h_sum_split
  exact h_sum_split

theorem prob_of_opposite {α : Type*} (P : ProbSpace α) : ∀ A ∈ P.F.sets, P.p (Aᶜ) = 1 - P.p A := by
  intros A h
  have hs : P.p Set.univ = P.p Aᶜ + P.p A := by
    have disj : Disjoint Aᶜ A := disjoint_compl_left
    have sigma : Aᶜ ∈ P.F.sets := P.F.compl_mem A h
    let add2 := p_add2 P sigma h disj
    simp at add2
    exact add2
  rw [P.p_univ] at hs
  apply_fun fun x => x - P.p A at hs
  simp at hs
  exact hs.symm

theorem prob_mono {α : Type*} (P : ProbSpace α) {A B : Set α}
    (hA : A ∈ P.F.sets) (hB : B ∈ P.F.sets) (hAB : A ⊆ B)
    : P.p A ≤ P.p B := by
    have hB_eq : B = A ∪ (B \ A) := by
      simp [Set.union_diff_self]
      rw [Eq.comm]
      rwa [Set.union_eq_right]
    rw [hB_eq]

    have h_diff : B \ A ∈ P.F.sets := by
      rw [Set.diff_eq]
      exact
        SigmaAlgebra.intersect2_mem P.F hB
        (SigmaAlgebra.compl_mem P.F A hA)

    have disj : Disjoint A (B \ A) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      simp[Set.diff_eq]
      rw [<- Set.inter_comm]
      rw [Set.inter_assoc]
      simp

    rw [p_add2 P hA h_diff disj]
    have h_nonneg : 0 ≤ P.p (B \ A) := P.p_nonneg (B \ A) h_diff
    linarith [h_nonneg]

theorem prob_max {α : Type*} {P : ProbSpace α} {A : Set α}
  (hA : A ∈ P.F.sets) : P.p A ≤ 1 := by
  rw [<- P.p_univ]
  apply prob_mono P hA P.F.univ_mem (Set.subset_univ A)
