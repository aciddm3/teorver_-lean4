import Mathlib.Data.Set.Basic
  -- Set α, ∪, ∩, ᶜ, ⊆, univ, ∅, Set.ext
import Mathlib.Tactic
  -- simp, rw, exact, have, calc, intro

-- сигма алгебра
structure SigmaAlgebra (Ω : Type*) where
  sets : Set (Set Ω)
  univ_mem : Set.univ ∈ sets
  compl_mem : ∀ s ∈ sets, sᶜ ∈ sets
  iUnion_mem : ∀ s : Nat → Set Ω, (∀ i, s i ∈ sets) → (⋃ i, s i) ∈ sets

theorem sigma_algebra_empty_mem {T : Type*} (F : SigmaAlgebra T) : ∅ ∈ F.sets := by
  have hav1 : Set.univ ∈ F.sets := by exact F.univ_mem
  have h_compl : Set.univᶜ ∈ F.sets := by exact F.compl_mem Set.univ hav1
  rw [Set.compl_univ] at h_compl
  exact h_compl

theorem sigma_algebra_iintersect_mem {T : Type*} (F : SigmaAlgebra T) :
  ∀ s : Nat → Set T, (∀ i, s i ∈ F.sets) → (⋂i, s i) ∈ F.sets := by
  intro s h_s
  have h_compl : ∀ i, (s i)ᶜ ∈ F.sets := by
    intro i
    exact F.compl_mem (s i) (h_s i)
  have h_union : (⋃ i, (s i)ᶜ) ∈ F.sets :=
    F.iUnion_mem (fun i => (s i)ᶜ) h_compl
  have h_compl_union : (⋃ i, (s i)ᶜ)ᶜ ∈ F.sets :=
    F.compl_mem _ h_union
  rw [Set.compl_iUnion] at h_compl_union
  simp at h_compl_union  -- убирает двойное дополнение ((s i)ᶜ)ᶜ → s i
  exact h_compl_union

def PowerSetSigmaAlgebra (Ω : Type*) : SigmaAlgebra Ω where
-- сигма алгебра - множество всех подмножеств
  sets := Set.univ
  univ_mem := by simp
  iUnion_mem := by simp
  compl_mem := by simp
