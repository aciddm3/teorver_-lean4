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
import Mathlib.Tactic.Linarith
  -- автоматизация линейных неравенств
import Mathlib.Tactic.FieldSimp
  -- упрощение выражений в полях (ℝ)
import Mathlib.Topology.Algebra.InfiniteSum.Basic

import Teorver.SigmaAlgebra


structure ProbSpace (Ω : Type*) where
  F : SigmaAlgebra Ω
  p : Set Ω → Real                      -- 1. Определяем на всех подмножествах
  p_nonneg : ∀ s ∈ F.sets, 0 ≤ p s      -- 2. Неотрицательность
  p_univ : p Set.univ = 1               -- 3. Нормировка на полном множестве
  p_add : ∀ (f : Nat → Set Ω),          -- 4. σ-аддитивность
    (∀ n, f n ∈ F.sets) →
    (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
    p (⋃ n, f n) = ∑' n, p (f n)


open Topology

theorem p_empty_eq_zero {T : Type*} (P : ProbSpace T) : P.p ∅ = 0 := by
  -- 1. Применяем счётную аддитивность к последовательности ∅
  have h := P.p_add (fun _ => ∅)
    (fun _ => sigma_algebra_empty_mem P.F)
    (by simp [Disjoint])
  -- h : P.p (⋃ n, ∅) = ∑' n, P.p ∅

  -- 2. ⋃ n, ∅ = ∅
  simp [Set.iUnion_const] at h
  -- h : P.p ∅ = ∑' n, P.p ∅

  -- 3. Разбиваем сумму: ∑' f n = f 0 + ∑' f (n+1)
  have h_shift : ∑' n : ℕ, P.p ∅ = P.p ∅ + ∑' n : ℕ, P.p ∅ := by
    rw [tsum_nat_eq 1]           -- стабильная лемма в Mathlib4
    simp [Finset.sum_range_one]  -- ∑_{i∈{0}} f i = f 0
    congr! 1                     -- доказываем f (n+1) ≡ f n
    ext n; simp

  -- 4. Подставляем и решаем x = x + x ⇒ x = 0
  rw [h_shift] at h
  linarith
