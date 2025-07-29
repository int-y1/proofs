import Mathlib.Logic.Basic

/-- This definition was copied from `Set` in `Mathlib.Data.Set.Defs`.
There are differences between `XSet` and mathematical sets. -/
def XSet (α : Type u) := α → Prop

namespace XSet

variable (A B : XSet α)

/-- This instance makes `∈` and `∉` available. -/
instance : Membership α (XSet α) :=
  ⟨fun A x ↦ A x⟩

-- Note: Axiom 3.1 allows expressions like `A ∈ B ∨ B ∈ A`.
-- But this goes against `XSet`'s design, because writing `A ∈ B ∨ B ∈ A` results in a type error.
-- It gets worse. Axiom 3.1 allows `A ∈ A` (using `A = B`), but `XSet` can't express `A ∈ A`.

/-- Axiom 3.2 -/
theorem eq_iff : A = B ↔ (∀ x, x ∈ A → x ∈ B) ∧ (∀ x, x ∈ B → x ∈ A) := by
  constructor
  · intro h
    rw [h]
    exact ⟨fun _ h ↦ h, fun _ h ↦ h⟩
  · intro h
    funext x
    apply propext
    exact ⟨h.1 x, h.2 x⟩

/-- Axiom 3.3, explicit construction of ∅ -/
def empty : XSet α := fun _ ↦ False
notation "∅" => empty

/-- Axiom 3.3 -/
theorem ex_empty : ∃ A : XSet α, ∀ x, x ∉ A :=
  ⟨empty, fun _ h ↦ h⟩

/-- Lemma 3.1.5. This is the first point where `Classical.choice` is needed. -/
theorem nonempty_has_element (h : A ≠ ∅) : ∃ x, x ∈ A := by
  refine' not_forall_not.1 fun h' ↦ _
  apply h
  apply (eq_iff _ _).2
  exact ⟨fun x h ↦ h' x h, fun _ h ↦ h.elim⟩

/-- Axiom 3.4, explicit construction of {a} -/
def singleton (a : α) : XSet α := fun y ↦ y = a

/-- Axiom 3.4 -/
theorem ex_singleton (a : α) : ∃ A : XSet α, ∀ y, y ∈ A ↔ y = a :=
  ⟨singleton a, fun _ ↦ ⟨id, id⟩⟩
