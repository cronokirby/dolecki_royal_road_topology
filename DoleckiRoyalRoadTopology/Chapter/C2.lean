import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice

import DoleckiRoyalRoadTopology.Set.Util

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

/-- Filters can be given an ordering, based on inclusion between the underlying collections. -/
instance : LE (Filter α) := { le := fun (F G) => F.sets ⊆ G.sets }

/-- Allow the shorthand x ∈ F, to say that x is one of the sets in F. -/
instance : Membership (Set α) (Filter α) := ⟨fun (F x) => x ∈ F.sets⟩

/-- A technical lemma extending the meet property from two sets to any finite number of sets.

This can be generalized quite a bit.
-/
lemma has_finite_meets {F : Filter α} {X : Set (Set α)} {X_fin : X.Finite} : (X_sub_F : ∀ x ∈ X, x ∈ F) → ⋂₀ X ∈ F := by
  apply Set.inter_to_sInter_extension
  . exact F.has_univ
  . exact F.meet
  . exact X_fin

class Proper (F : Filter α) : Prop where
  no_empty_set : ∅ ∉ F.sets

/-- A collection is a base fo r a filter, if its upper closure provides the colleciton of sets of F.-/
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

/-- The kernel of a filter is the bottom set of its collection.

A filter does not necessarily contain its kernel, since only finite
meets are guaranteed to be in the filter.
-/
def Kernel (F : Filter α) : Set α := ⋂ X ∈ F, X

/-- A filter is free when its kernel is empty. -/
def Free (F : Filter α) : Prop := F.Kernel = ∅

lemma free_contains_cofinite {F : Filter α} : F.Free → (Cofinite α) ≤ F := by
  intro h
  have l1 (x) : {x}ᶜ ∈ F := by sorry
  have l2 (A) (_ : A.Finite) : Aᶜ ∈ F := by sorry
  have l3 (B) (h_B : Bᶜ.Finite) : B ∈ F := by
    suffices Bᶜᶜ ∈ F by
      rw [compl_compl] at this
      exact this
    exact l2 Bᶜ h_B
  exact l3

end Filter
