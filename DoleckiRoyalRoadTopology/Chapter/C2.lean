import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic

/-- The upper closure of a set contains all elements above that in the original set.

This is useful in defining the notion of a FilterBase, among other things.
-/
def Set.upper_closure (X : Set (Set α)) : Set (Set α) :=
  {a : Set α | ∃ x ∈ X, x ⊆ a}

structure Filter (α) where
  /-- A filter is a collection of subsets of α. -/
  sets : Set (Set α)

  /-- The isotone property makes a filter upwardly closed. -/
  isotone : x ∈ sets → x ⊆ y → y ∈ sets

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
  F.sets = base.upper_closure
