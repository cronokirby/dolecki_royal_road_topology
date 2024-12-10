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

  /-- The isotone property makes a filter upwardly closed. -/
  isotone : ∀ {x y : Set α}, x ⊆ y → x ∈ sets → y ∈ sets

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
    intro x y x_sub_y h_x
    suffices yᶜ ⊆ xᶜ by
      exact Set.Finite.subset h_x this
    exact Set.compl_subset_compl.mpr x_sub_y
  meet := by
    intros
    simp_all only [Set.mem_setOf, Set.compl_inter, Set.Finite.union]
  has_univ := by simp
}

/-- The kernel of a filter is the bottom set of its collection.

A filter does not necessarily contain its kernel, since only finite
meets are guaranteed to be in the filter.
-/
def Kernel (F : Filter α) : Set α := ⋂₀ F.sets

/-- A filter is free when its kernel is empty. -/
def Free (F : Filter α) : Prop := F.Kernel = ∅

lemma free_contains_cofinite {F : Filter α} : F.Free → (Cofinite α) ≤ F := by
  intro h
  have l1 (x) : {x}ᶜ ∈ F := by
    have F_free : x ∉ F.Kernel := by
      rw [h]
      exact Set.not_mem_empty x
    have ⟨X, ⟨X_in_F, _⟩⟩ : ∃ X ∈ F, x ∉ X := by
      by_contra h
      rw [not_exists] at h
      have h0 : ∀ Y ∈ F, x ∈ Y := by
        intro Y h_Y
        let h0 := h Y
        rw [not_and_not_right] at h0
        exact h0 h_Y
      apply Set.mem_sInter.mpr at h0
      have h1 : x ∉ ⋂₀ F.sets := by exact F_free
      simp_all only [not_and, not_not]
    suffices X ⊆ {x}ᶜ by
      apply F.isotone this X_in_F
    apply Set.subset_compl_singleton_iff.mpr
    assumption
  have l2 (A) (A_fin : A.Finite) : Aᶜ ∈ F := by
    let f : α → Set α := fun (a) => {a}ᶜ
    let X : Set (Set α) := f '' A
    suffices Aᶜ = ⋂₀ X by
      rw [this]
      apply F.has_finite_meets
      . suffices ∀ a, {a}ᶜ ∈ F by
          intro x h_x
          let ⟨a, ⟨_, a_compl_eq_x⟩⟩ := h_x
          rw [←a_compl_eq_x]
          apply this
        exact l1
      . exact Set.Finite.image f A_fin
    simp_all only [Set.sInter_image, X, f]
    ext x : 1
    simp_all only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_singleton_iff]
    apply Iff.intro
    · intro a i i_1
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      subst a_1
      simp_all only [not_true_eq_false]
    · intro a
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      apply a
      · exact a_1
      · simp_all only
  have l3 (B) (h_B : Bᶜ.Finite) : B ∈ F := by
    suffices Bᶜᶜ ∈ F by
      rw [compl_compl] at this
      exact this
    exact l2 Bᶜ h_B
  exact l3

/-- The pushforward lets us create a filter on a target type by using a function. -/
def Pushforward (φ : α → β) (F : Filter α) : Filter β :=
  {
    sets := {X : Set β | φ⁻¹' X ∈ F.sets },
    has_univ := by
      simp_all only [Set.mem_setOf_eq, Set.preimage_univ]
      exact F.has_univ
    meet := by
      intro x y h0 h1
      simp_all only [Set.mem_setOf_eq, Set.preimage_inter]
      exact F.meet h0 h1
    isotone := by
      intro x y x_sub_y x_in_F
      simp_all only [Set.mem_setOf_eq]
      suffices φ⁻¹' x ⊆ φ⁻¹' y by
        apply F.isotone this x_in_F
      rw [Set.subset_def]
      intro a h_a
      rw [Set.mem_preimage]
      apply x_sub_y
      exact h_a
  }

notation:1000 arg:1000 "↱" => Filter.Pushforward arg
end Filter
