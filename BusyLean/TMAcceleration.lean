import BusyLean.TM

/-!
# Turing machine acceleration

Helper functions to help create accelerated TM rules.
-/

open Turing

variable {Q : Type u}     -- The type of states
variable {Sym : Type v}   -- The type of tape symbols
variable (l l₁ l₂ : List Sym)
variable (s₁ s₂ s₃ : Sym)
variable (n m : Nat)


/-!
## Compressed tapes by using `^`
-/

instance : HPow (List Sym) Nat (List Sym) := ⟨fun l n ↦ n.repeat (l ++ ·) []⟩

@[simp]
theorem list_pow_zero : l^0 = [] := by rfl

@[simp]
theorem list_pow_one : l^1 = l := by
  simp_rw [HPow.hPow, Nat.repeat, List.append_nil]

theorem list_pow_two : l^2 = l ++ l := by
  simp_rw [HPow.hPow, Nat.repeat, List.append_nil]

theorem list_pow_add : l^(n + m) = l^n ++ l^m := by
  revert n
  induction' m with m ih <;> intro n
  · rw [list_pow_zero, List.append_nil, add_zero]
  · simp_rw [add_comm m 1, ← add_assoc, ih, ← List.append_assoc, List.append_cancel_right_eq,
      list_pow_one, HPow.hPow, Nat.repeat]
    induction' n with n ih
    · simp_rw [Nat.repeat, List.append_nil, List.nil_append]
    · simp_rw [Nat.repeat, List.append_assoc, ih]

theorem list_pow_mul : l^(n * m) = (l^n)^m := by
  revert n
  induction' m with m ih <;> intro n
  · rfl
  · simp_rw [Nat.mul_add, mul_one, list_pow_add, list_pow_one, ih]

variable [Inhabited Sym]  -- The fact that `Sym` is nonempty. Use `default` to get the inhabitant.
                          -- By convention, the blank symbol is used as the inhabitant.
variable (side : ListBlank Sym)

theorem list1_append_eq : [s₁]^(n + 1) +> side = [s₁]^n +> s₁ >> side := by
  rw [list_pow_add, list_pow_one, ListBlank.append_assoc]; rfl

theorem list1_append_eq':
    [s₁]^(n + 1) +> side = s₁ >> [s₁]^n +> side := by
  rw [add_comm, list_pow_add, list_pow_one, ListBlank.append_assoc]; rfl

theorem list2_append_eq : [s₁, s₂]^(n + 1) +> side = [s₁, s₂]^n +> s₁ >> s₂ >> side := by
  rw [list_pow_add, list_pow_one, ListBlank.append_assoc]; rfl

theorem list2_append_eq' : [s₁, s₂]^(n + 1) +> side = s₁ >> s₂ >> [s₁, s₂]^n +> side := by
  rw [add_comm, list_pow_add, list_pow_one, ListBlank.append_assoc]; rfl

theorem list2_rotate : [s₁, s₂]^n +> s₁ >> side = s₁ >> [s₂, s₁]^n +> side := by
  simp_rw [HPow.hPow]
  induction' n with n ih
  · rfl
  · simp_rw [Nat.repeat, ListBlank.append_assoc, ih]; rfl

theorem list3_append_eq :
    [s₁, s₂, s₃]^(n + 1) +> side = [s₁, s₂, s₃]^n +> s₁ >> s₂ >> s₃ >> side := by
  rw [list_pow_add, list_pow_one, ListBlank.append_assoc]; rfl

theorem list3_append_eq' :
    [s₁, s₂, s₃]^(n + 1) +> side = s₁ >> s₂ >> s₃ >> [s₁, s₂, s₃]^n +> side := by
  rw [add_comm, list_pow_add, list_pow_one, ListBlank.append_assoc]; rfl

theorem list3_rotate : [s₁, s₂, s₃]^n +> s₁ >> side = s₁ >> [s₂, s₃, s₁]^n +> side := by
  simp_rw [HPow.hPow]
  induction' n with n ih
  · rfl
  · simp_rw [Nat.repeat, ListBlank.append_assoc, ih]; rfl


/-!
## Accelerated rules
-/

variable (tm : @TM Q Sym)
variable (q : Q)
variable (side₁ side₂ : ListBlank Sym)

/-- If `l₁ <{q} ⊢* <{q} l₂` then `l₁^n <{q} ⊢* <{q} l₂^n`. -/
theorem step_lq_ql_repeat
    (h : ∀ side₁ side₂, (side₁ <+ l₁ <{{q}} side₂) [tm]⊢* side₁ <{{q}} l₂ +> side₂) :
    (side₁ <+ l₁^n <{{q}} side₂) [tm]⊢* side₁ <{{q}} l₂^n +> side₂ := by
  revert side₁ side₂
  induction' n with n ih <;> intros side₁ side₂
  · finish
  nth_rw 3 [add_comm]
  simp_rw [list_pow_add, list_pow_one, Turing.ListBlank.append_assoc]
  refine stepStar_trans (ih _ _) ?_
  refine stepStar_trans (h _ _) ?_
  finish

/-- If `{q}> l₁ ⊢* l₂ {q}>` then `{q}> l₁^n ⊢* l₂^n {q}>`. -/
theorem step_ql_lq_repeat
    (h : ∀ side₁ side₂, (side₁ {{q}}> l₁ +> side₂) [tm]⊢* side₁ <+ l₂ {{q}}> side₂) :
    (side₁ {{q}}> l₁^n +> side₂) [tm]⊢* side₁ <+ l₂^n {{q}}> side₂ := by
  revert side₁ side₂
  induction' n with n ih <;> intros side₁ side₂
  · finish
  nth_rw 3 [add_comm]
  simp_rw [list_pow_add, list_pow_one, Turing.ListBlank.append_assoc]
  refine stepStar_trans (ih _ _) ?_
  refine stepStar_trans (h _ _) ?_
  finish
