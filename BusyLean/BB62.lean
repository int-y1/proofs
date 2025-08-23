import Mathlib.Computability.TuringMachine
import BusyLean.TM

/-!
# Instantiating the development to machines with 6 states and 2 symbols

This file is similar to `BusyLean.BB52`.
-/

inductive State
  | A | B | C | D | E | F

inductive Symbol
  | S0 | S1

open Turing State Symbol

instance : Inhabited State := ⟨A⟩

instance : OfNat Symbol 0 := ⟨S0⟩
instance : OfNat Symbol 1 := ⟨S1⟩
instance : Inhabited Symbol := ⟨0⟩

-- TODO: Is there a way to simplify this?
notation3:60 l:65 " <{{A}} " r:65 => l <{{A}} r
notation3:60 l:65 " <{{B}} " r:65 => l <{{B}} r
notation3:60 l:65 " <{{C}} " r:65 => l <{{C}} r
notation3:60 l:65 " <{{D}} " r:65 => l <{{D}} r
notation3:60 l:65 " <{{E}} " r:65 => l <{{E}} r
notation3:60 l:65 " <{{F}} " r:65 => l <{{F}} r
notation3:60 l:65 " {{A}}> " r:65 => l {{A}}> r
notation3:60 l:65 " {{B}}> " r:65 => l {{B}}> r
notation3:60 l:65 " {{C}}> " r:65 => l {{C}}> r
notation3:60 l:65 " {{D}}> " r:65 => l {{D}}> r
notation3:60 l:65 " {{E}}> " r:65 => l {{E}}> r
notation3:60 l:65 " {{F}}> " r:65 => l {{F}}> r

notation3 "Side" => ListBlank Symbol
notation3 "TM62" => @TM State Symbol

@[simp]
def list_nat_repeat (l : List α) (n : Nat) := match n with
  | 0 => []
  | n + 1 => List.append l (list_nat_repeat l n)

instance instHPowListNat : HPow (List Symbol) Nat (List Symbol) := ⟨list_nat_repeat⟩

@[simp]
theorem list_pow_zero (l : List Symbol) : l^0 = [] := by rfl

@[simp]
theorem list_pow_one (l : List Symbol) : l^1 = l := by
  simp_rw [HPow.hPow, list_nat_repeat, List.append_eq, List.append_nil]

theorem list_pow_add (l : List Symbol) (n m : Nat) : l^(n + m) = l^n ++ l^m := match m with
  | 0 => by
    rw [list_pow_zero, List.append_nil, add_zero]
  | m + 1 => by
    rw [add_comm m 1, ← add_assoc, add_comm 1 m, list_pow_add]
    simp_rw [HPow.hPow, list_nat_repeat, List.append_eq, List.append_assoc]
    rw [← List.append_assoc, ← List.append_assoc, List.append_cancel_right_eq]
    induction' n with n ih <;> [simp; simpa]
