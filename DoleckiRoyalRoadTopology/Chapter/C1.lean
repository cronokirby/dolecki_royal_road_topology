import Mathlib.Data.Set.Defs


/-- A relation between two types maps each α to a set of β.

This generalizes functions, by allowing no output for a given value,
or some output for a given value.
-/
structure Rel (α β : Type) where
  image : α → Set β

/-- The opposite relation tells us how the β correspond to sets of α. -/
def Rel.op (R : Rel α β) : Rel β α := {
  image := fun (b : β) => { a : α | b ∈ R.image a}
}

/-- The opposite of the opposite is the same relation. -/
theorem Rel.op_op_id {R : Rel α β} : R.op.op = R := rfl -- Wow!

def Rel.comp (S : Rel β γ) (R : Rel α β) : Rel α γ := {
  image := fun (a) => {c | ∃ b ∈ R.image a, c ∈ S.image b }
}

def Rel.graph (f : α → β) : Rel α β := { image := fun (a) => {f a} }

def Rel.Δ : Rel α α := Rel.graph id
