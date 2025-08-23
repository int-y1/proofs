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
notation "S0" => (0 : Symbol)
notation "S1" => (1 : Symbol)

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
