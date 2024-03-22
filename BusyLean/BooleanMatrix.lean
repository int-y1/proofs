import Mathlib.Data.Matrix.Notation
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Boolean matrices

This file contains helpers for `M_{n,n}(Two)`. This is the set of square matrices over `Two`, where
`Two` is the boolean semiring.

## Main declarations

* `Two`: Elements of the boolean semiring.
* `instOrderedCommSemiringTwo`: This is an upgraded version of `Semiring Two`.
* `instOrderedSemiringMatrixFinTwo`: `M_{n,n}(Two)` is an ordered semiring.
-/

/-- Elements of the boolean semiring. https://en.wikipedia.org/wiki/Two-element_Boolean_algebra

todo: find a better name for the boolean semiring -/
def Two := Fin 2

instance : Zero Two := ⟨(0 : Fin 2)⟩

instance : One Two := ⟨(1 : Fin 2)⟩

instance : Add Two := ⟨max (α := Fin 2)⟩

instance : Mul Two := ⟨min (α := Fin 2)⟩

/-- This is an upgraded version of `Semiring Two`. TODO: Clean up all the proofs. -/
instance instOrderedCommSemiringTwo : OrderedCommSemiring Two := {
  add_assoc := fun _ _ _ ↦ by simp_rw [HAdd.hAdd, Add.add, max_assoc]
  zero_add := fun _ ↦ by simp_rw [HAdd.hAdd, Add.add]; simp
  add_zero := fun _ ↦ by simp_rw [HAdd.hAdd, Add.add]; simp
  add_comm := fun _ _ ↦ by simp_rw [HAdd.hAdd, Add.add, max_comm]
  left_distrib := fun _ _ _ ↦ by
    simp_rw [HAdd.hAdd, Add.add, HMul.hMul, Mul.mul, min_max_distrib_left]
  right_distrib := fun _ _ _ ↦ by
    simp_rw [HAdd.hAdd, Add.add, HMul.hMul, Mul.mul, min_max_distrib_right]
  zero_mul := fun _ ↦ by simp_rw [HMul.hMul, Mul.mul]; simp
  mul_zero := fun _ ↦ by simp_rw [HMul.hMul, Mul.mul]; simp
  mul_assoc := fun _ _ _ ↦ by simp_rw [HMul.hMul, Mul.mul, min_assoc]
  one_mul := fun a ↦ by unfold Two at *; fin_cases a <;> simp
  mul_one := fun a ↦ by unfold Two at *; fin_cases a <;> simp
  le_refl := le_refl (α := Fin 2)
  le_trans := fun _ _ _ ↦ le_trans (α := Fin 2)
  le_antisymm := fun a b ↦ by unfold Two at *; exact le_antisymm
  add_le_add_left := fun a b h c ↦ by
    unfold Two at *; simp_rw [HAdd.hAdd, Add.add]
    fin_cases c <;> simp [h]
    fin_cases a <;> simp
  zero_le_one := by unfold Two; simp
  mul_le_mul_of_nonneg_left := fun a b c h _ ↦ by
    unfold Two at *; simp_rw [HMul.hMul, Mul.mul]
    fin_cases c <;> simp [h]
  mul_comm := fun a b ↦ by simp_rw [HMul.hMul, Mul.mul, min_comm]
  mul_le_mul_of_nonneg_right := fun a b c h _ ↦ by
    unfold Two at *; simp_rw [HMul.hMul, Mul.mul]
    fin_cases c <;> simp [h]
}

instance : LE (Matrix m n Two) := ⟨fun M N ↦ ∀ i j, LE.le (α := Fin 2) (M i j) (N i j)⟩

/-- `M_{n,n}(Two)` is an ordered semiring. -/
instance instOrderedSemiringMatrixFinTwo : OrderedSemiring (Matrix (Fin n) (Fin n) Two) := {
  le_refl := fun _ _ _ ↦ le_refl _
  le_trans := fun _ _ _ h₁ h₂ i j ↦ le_trans (h₁ i j) (h₂ i j)
  le_antisymm := fun _ _ h₁ h₂ ↦ by ext i j; exact le_antisymm (h₁ i j) (h₂ i j)
  add_le_add_left := fun _ _ h _ i j ↦ by
    simp_rw [Matrix.add_apply]
    exact add_le_add_left (α := Two) (h _ _) _
  zero_le_one := fun _ _ ↦ by simp only [Matrix.zero_apply, Fin.zero_le]
  mul_le_mul_of_nonneg_left := fun L M N h₁ h₂ i j ↦ by
    simp_rw [Matrix.mul_apply]
    apply Finset.sum_le_sum (f := fun k => N i k * L k j)
    intro k _
    exact mul_le_mul_of_nonneg_left (h₁ _ _) (h₂ _ _)
  mul_le_mul_of_nonneg_right := fun L M N h₁ h₂ i j ↦ by
    simp_rw [Matrix.mul_apply]
    apply Finset.sum_le_sum (f := fun k => L i k * N k j)
    intro k _
    exact mul_le_mul_of_nonneg_right (h₁ _ _) (h₂ _ _)
}

instance : DecidableEq Two := instDecidableEqFin _

instance : DecidableRel (α := Matrix (Fin m) (Fin n) Two) (· ≤ ·) :=
  fun _ _ ↦ Fintype.decidableForallFintype

--def mat1 : Matrix (Fin 3) (Fin 3) Two := !![1,1,0;0,0,0;0,0,0]
--def mat2 : Matrix (Fin 3) (Fin 3) Two := !![1,0,0;1,0,0;0,0,0]
--#eval mat1 * mat2  -- ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]]
--#eval mat1 ≤ mat2  -- false
