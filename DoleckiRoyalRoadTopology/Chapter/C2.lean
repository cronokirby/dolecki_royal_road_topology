import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic

section sets
/-
! This section contains a few useful constructions and theorems about sets
-/

/-- The upper closure of a set contains all elements above that in the original set.

This is useful in defining the notion of a FilterBase, among other things.
-/
def Set.upper_closure (X : Set (Set α)) : Set (Set α) :=
  {a : Set α | ∃ x ∈ X, x ⊆ a}


variable {X : Set (Set α)}

lemma Set.upper_closure_larger : X ⊆ X.upper_closure := by
  rw [Set.subset_def]
  intro x _
  apply Set.mem_setOf.mpr
  exists x

lemma Set.upper_closure_idempotent : X.upper_closure.upper_closure = X.upper_closure := by
  suffices X.upper_closure.upper_closure ⊆ X.upper_closure by
    apply Set.eq_of_subset_of_subset
    exact this
    exact Set.upper_closure_larger
  rw [Set.subset_def]
  intro x x_in_X_u_u
  have ⟨a, ⟨a_in_X_u, a_sub_x⟩⟩ : ∃ a ∈ X.upper_closure, a ⊆ x := x_in_X_u_u.out
  have ⟨b, ⟨b_in_X, b_sub_a⟩⟩ : ∃ b ∈ X, b ⊆ a := a_in_X_u.out
  apply Set.mem_setOf.mpr
  exists b
  apply And.intro b_in_X
  exact Set.Subset.trans b_sub_a a_sub_x
end sets

structure Filter (α) where
  /-- A filter is a collection of subsets of α. -/
  sets : Set (Set α)

  /-- The isotone property makes a filter upwardly closed. -/
  isotone : sets.upper_closure = sets

  /-- The meet property gives us some downward reachingness. -/
  meet : (x ∈ sets) → (y ∈ sets) → x ∩ y ∈ sets

  /-- We work with non-degenerate filters, so we require inhabitation.

  Because of the isotone property, we might as well use the universe as the given element.
  -/
  has_univ : Set.univ ∈ sets

class Filter.Proper (F : Filter α): Prop where
  no_empty_set : ∅ ∉ F.sets

/-- A collection is a base for a filter, if its upper closure provides the colleciton of sets of F.-/
def Filter.has_base {F : Filter α} (base : Set (Set α)) : Prop :=
  base.upper_closure = F.sets
