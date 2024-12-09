import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic

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

  /-- The isotone property makes a filter upwardly closed.

  We have this as saying that the upper closure is contained in the sets.
  By definition, the upper closure will also contain the sets, so these are equal,
  but this avoids the need to prove a trivial statement over and over when constructing filters.
  -/
  isotone : sets.upper_closure ⊆ sets

  /-- The meet property gives us some downward reachingness. -/
  meet : (x ∈ sets) → (y ∈ sets) → x ∩ y ∈ sets

  /-- We work with non-degenerate filters, so we require inhabitation.

  Because of the isotone property, we might as well use the universe as the given element.
  -/
  has_univ : Set.univ ∈ sets

namespace Filter

class Proper (F : Filter α) : Prop where
  no_empty_set : ∅ ∉ F.sets

/-- A collection is a base for a filter, if its upper closure provides the colleciton of sets of F.-/
def has_base (F : Filter α) (base : Set (Set α)) : Prop :=
  base.upper_closure = F.sets

/-- A filter is *principal* if there exists a single set generating it.

Because this follows directly from there being a finite base, because of the meet
property, we instead use the simpler definition.
-/
def Principal (F : Filter α) : Prop := ∃ B : Set α, F.has_base {B}

/-- Given a set, we can filter out the finite subsets of the set. -/
def Cofinite (α : Type) : Filter α := {
  sets := {x : Set α | xᶜ.Finite },
  isotone := by
    apply Set.subset_setOf.mpr
    intro x h_x
    have ⟨y, ⟨y_cof, y_sub_x⟩⟩ : ∃ y : Set α, yᶜ.Finite ∧ y ⊆ x := h_x
    suffices xᶜ ⊆ yᶜ by
      apply Set.Finite.subset y_cof
      exact this
    exact Set.compl_subset_compl.mpr y_sub_x
  meet := by
    intro x y h_x h_y
    apply Set.mem_setOf.mp at h_x
    apply Set.mem_setOf.mp at h_y
    apply Set.mem_setOf.mpr
    rw [Set.compl_inter]
    exact Set.Finite.union h_x h_y
  has_univ := by simp
}

/-- Filters can be given an ordering, based on inclusion between the underlying collections. -/
instance : LE (Filter α) := { le := fun (a b : Filter α) => a.sets ⊆ b.sets }

end Filter
