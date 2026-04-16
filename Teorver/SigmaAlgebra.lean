import Mathlib.Data.Set.Basic
  -- Set α, ∪, ∩, ᶜ, ⊆, univ, ∅, Set.ext
import Mathlib.Tactic
  -- simp, rw, exact, have, calc, intro

-- сигма алгебра
structure SigmaAlgebra (Ω : Type*) where
  sets : Set (Set Ω)
  univ_mem : Set.univ ∈ sets
  compl_mem : ∀ s ∈ sets, sᶜ ∈ sets
  iUnion_mem : ∀ s : Nat -> Set Ω, (∀ i, s i ∈ sets) -> (⋃ i, s i) ∈ sets

namespace SigmaAlgebra

theorem empty_mem {T : Type*} (F : SigmaAlgebra T)
: ∅ ∈ F.sets := by
  have hav1 : Set.univ ∈ F.sets := by exact F.univ_mem
  have h_compl : Set.univᶜ ∈ F.sets := by exact F.compl_mem Set.univ hav1
  rw [Set.compl_univ] at h_compl
  exact h_compl

theorem iintersect_mem {T : Type*} (F : SigmaAlgebra T) :
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
  simp at h_compl_union -- убирает двойное дополнение ((s i)ᶜ)ᶜ → s i
  exact h_compl_union

theorem intersect2_mem {T : Type*} (F : SigmaAlgebra T) {A B : Set T}
  : (A ∈ F.sets) -> (B ∈ F.sets) -> (A ∩ B ∈ F.sets) := by
    intro hA hB
    let seq n := if n=0 then A else if n=1 then B else Set.univ
    have seq_mem : (⋂i, seq i) ∈ F.sets := by
      have hav1 : ∀ i, seq i ∈ F.sets := by
        intro n
        rcases n with _|_|_
        . simp[seq]
          exact hA
        . simp[seq]
          exact hB
        . simp[seq]
          exact F.univ_mem
      apply F.iintersect_mem seq hav1
    rw [<-Set.inter_iInter_nat_succ,
      <-Set.inter_iInter_nat_succ] at seq_mem
    simp [seq] at seq_mem
    exact seq_mem

def PowerSetSigmaAlgebra (Ω : Type*) : SigmaAlgebra Ω where
-- сигма алгебра - множество всех подмножеств
  sets := Set.univ
  univ_mem := by simp
  iUnion_mem := by simp
  compl_mem := by simp
