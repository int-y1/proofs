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
