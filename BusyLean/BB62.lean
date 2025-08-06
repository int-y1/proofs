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

notation3 l " <{{A}} " r => (A, (⟨ListBlank.head l, ListBlank.tail l, r⟩ : Tape _))
notation3 l " <{{B}} " r => (B, (⟨ListBlank.head l, ListBlank.tail l, r⟩ : Tape _))
notation3 l " <{{C}} " r => (C, (⟨ListBlank.head l, ListBlank.tail l, r⟩ : Tape _))
notation3 l " <{{D}} " r => (D, (⟨ListBlank.head l, ListBlank.tail l, r⟩ : Tape _))
notation3 l " <{{E}} " r => (E, (⟨ListBlank.head l, ListBlank.tail l, r⟩ : Tape _))
notation3 l " <{{F}} " r => (F, (⟨ListBlank.head l, ListBlank.tail l, r⟩ : Tape _))
notation3 l " {{A}}> " r => (A, (⟨ListBlank.head r, l, ListBlank.tail r⟩ : Tape _))
notation3 l " {{B}}> " r => (B, (⟨ListBlank.head r, l, ListBlank.tail r⟩ : Tape _))
notation3 l " {{C}}> " r => (C, (⟨ListBlank.head r, l, ListBlank.tail r⟩ : Tape _))
notation3 l " {{D}}> " r => (D, (⟨ListBlank.head r, l, ListBlank.tail r⟩ : Tape _))
notation3 l " {{E}}> " r => (E, (⟨ListBlank.head r, l, ListBlank.tail r⟩ : Tape _))
notation3 l " {{F}}> " r => (F, (⟨ListBlank.head r, l, ListBlank.tail r⟩ : Tape _))

notation3 "Side" => ListBlank Symbol
notation3 "TM62" => @TM State Symbol

@[simp]
def list_nat_repeat (l : List α) (n : Nat) := match n with
  | 0 => []
  | n + 1 => List.append l (list_nat_repeat l n)

instance instHPowListNat : HPow (List Symbol) Nat (List Symbol) := ⟨list_nat_repeat⟩

theorem list_pow_add (l : List Symbol) (n m : Nat) : l^(n + m) = l^n ++ l^m := match m with
  | 0 => by
    simp_rw [HPow.hPow, add_zero, list_nat_repeat, List.append_nil]
  | m + 1 => by
    rw [add_comm m 1, ← add_assoc, add_comm 1 m, list_pow_add]
    simp only [HPow.hPow, list_nat_repeat, List.append_eq, List.append_assoc]
    rw [← List.append_assoc, ← List.append_assoc, List.append_cancel_right_eq]
    induction' n with n ih <;> [simp; simpa]
