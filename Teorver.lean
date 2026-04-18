import Teorver.Basic
import Mathlib.Data.Set.Finite.Lemmas
-- Пространство исходов: (Орёл/Решка) × (Орёл/Решка)
abbrev Ω := Bool × Bool

-- Вероятность: равномерная на 4 исходах
def coin2 : ProbSpace Ω where
  F := SigmaAlgebra.PowerSetSigmaAlgebra Ω
  p := fun s => (s.toFinset.card : ℝ) / 4
  p_nonneg := by
    intro s _
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  p_univ := by simp;
  p_add := by
    intro seq h_mem h_disj
    /- 1. Доказываем конечность носителя {n | seq n ≠ ∅} -/
    have h_fin : Set.Finite {n | seq n ≠ ∅} := by
      sorry
      -- Каждому непустому seq n сопоставляем произвольный элемент из него.
      -- Из-за дизъюнктности разные n дают разные элементы → носитель вкладывается в конечное Ω.
      /-
      apply Set.Finite.subset (Set.finite_range (fun n => Classical.choose (by simp [Set.mem_setOf_eq] at ‹_›; exact ‹_›)))
      intro n hn
      simp [Set.mem_range]
      use Classical.choose hn
      simp [Classical.choose_spec hn]
      -/

    /- 2. Бесконечная сумма сводится к конечной по носителю -/
    have h_tsum_eq_sum : ∑' n, (seq n).toFinset.card = ∑ n ∈  h_fin.toFinset, (seq n).toFinset.card := by
      apply Set.Finite.tdu h_fin
      intro n hn
      simp [hn]

    /- 3. Кардинальность объединения = сумме кардинальностей (конечное дизъюнктное объединение) -/
    have h_card_union : (⋃ n, seq n).toFinset.card = ∑ n in h_fin.toFinset, (seq n).toFinset.card := by
      rw [← Finset.card_biUnion]
      · congr! 1; ext x; simp [Set.mem_iUnion]
      · intro i hi j hj h_ne; exact (h_disj i j h_ne).symm

    /- 4. Делим на 4 и закрываем цель -/
    simp only [p]
    rw [← h_card_union, h_tsum_eq_sum]

#eval coin2.p {omega | omega.1 = true }
