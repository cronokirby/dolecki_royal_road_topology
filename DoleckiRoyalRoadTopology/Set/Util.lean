/-
! This module contains some utilities related to sets, useful in the rest of the book.
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice

/-- Given a property that is stable across the intersection of two sets, generalize it to finitely many sets -/
def Set.inter_to_sInter_extension
  {P : Set α → Prop}
  {P_univ : P (Set.univ)}
  {P_inter : {x y : Set α} → (P x) → (P y) → P (x ∩ y)}
  {X : Set (Set α)}
  {X_fin : X.Finite} :
  (∀ x ∈ X, P x) → P (⋂₀ X) := by
    let C (Y : Set _) : Prop := (∀ y ∈ Y, P y) → P (⋂₀ Y)
    have i_0 : C ∅ := by
      have h : ⋂₀ ∅ = (Set.univ : Set α) := by
        ext x : 1
        simp_all only [Set.mem_sInter, Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true, Set.mem_univ]
      intro _
      rw [h]
      exact P_univ
    have i_1 : ∀ {a : Set α} {S : Set (Set α)}, a ∉ S → S.Finite → C S → C (insert a S) := by
      intro a S _ _ C_S
      intro all_in
      suffices P (a ∩ ⋂₀ S) by
        rw [Set.sInter_insert]
        exact this
      apply P_inter
      . rw [Set.forall_mem_insert] at all_in
        exact all_in.left
      . rw [Set.forall_mem_insert] at all_in
        apply C_S
        exact all_in.right
    exact Set.Finite.induction_on X_fin i_0 i_1
