import Mathlib.Computability.TuringMachine
import BusyLean.TM

/-!
# Instantiating the development to machines with 5 states and 2 symbols

Original source: https://github.com/meithecatte/busycoq/blob/master/verify/BB52.v
-/

inductive State
  | A | B | C | D | E

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
notation3 l " {{A}}> " r => (A, (⟨ListBlank.head r, l, ListBlank.tail r⟩ : Tape _))
notation3 l " {{B}}> " r => (B, (⟨ListBlank.head r, l, ListBlank.tail r⟩ : Tape _))
notation3 l " {{C}}> " r => (C, (⟨ListBlank.head r, l, ListBlank.tail r⟩ : Tape _))
notation3 l " {{D}}> " r => (D, (⟨ListBlank.head r, l, ListBlank.tail r⟩ : Tape _))
notation3 l " {{E}}> " r => (E, (⟨ListBlank.head r, l, ListBlank.tail r⟩ : Tape _))

notation3 "Side" => ListBlank Symbol
notation3 "TM52" => @TM State Symbol
