import Mathlib.Data.Set.Defs

/-- A relation between two types maps each α to a set of β.

This generalizes functions, by allowing no output for a given value,
or some output for a given value.
-/
structure Rel (α β) where
  image : α → Set β

/-- The opposite relation tells us how the β correspond to sets of α. -/
def Rel.op (R : Rel α β) : Rel β α := {
  image := fun (b : β) => { a : α | b ∈ R.image a}
}

#check ∀ (α β : Type) (R : Rel α β), R.op.op = R
