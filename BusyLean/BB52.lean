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

-- TODO: Is there a way to simplify this?
notation3:60 l:65 " <{{A}} " r:65 => l <{{A}} r
notation3:60 l:65 " <{{B}} " r:65 => l <{{B}} r
notation3:60 l:65 " <{{C}} " r:65 => l <{{C}} r
notation3:60 l:65 " <{{D}} " r:65 => l <{{D}} r
notation3:60 l:65 " <{{E}} " r:65 => l <{{E}} r
notation3:60 l:65 " {{A}}> " r:65 => l {{A}}> r
notation3:60 l:65 " {{B}}> " r:65 => l {{B}}> r
notation3:60 l:65 " {{C}}> " r:65 => l {{C}}> r
notation3:60 l:65 " {{D}}> " r:65 => l {{D}}> r
notation3:60 l:65 " {{E}}> " r:65 => l {{E}}> r

notation3 "Side" => ListBlank Symbol
notation3 "TM52" => @TM State Symbol
