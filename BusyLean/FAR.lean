import Mathlib.Computability.TuringMachine
import Mathlib.Data.List.DropRight
import BusyLean.BooleanMatrix

/-!
# Finite automata reduction

wip
-/

open Turing

variable {Q : Type u} {Sym : Type v} [Inhabited Q] [DecidableEq Sym] [Inhabited Sym] (tm : @TM Q Sym)
  (c c₁ c₂ c₃ : Q × Tape Sym)

namespace Turing.ListBlank

/-- Remove the default symbol from the end of `l`. -/
def truncateList (l : List Sym) : List Sym :=
  l.rdropWhile (· = default)

/-- Given a `ListBlank`, find an element of its equivalence class.
This is the inverse of `ListBlank.mk`. -/
def toList (l : ListBlank Sym) : List Sym := l.liftOn truncateList <| by
  rintro a - ⟨n, rfl⟩
  simp_rw [truncateList, List.rdropWhile, List.reverse_append, List.reverse_replicate,
    List.dropWhile_append]
  suffices (List.replicate n (default : Sym)).dropWhile (· = default) = [] by rw [this]; rfl
  simp_rw [List.dropWhile_eq_nil_iff, decide_eq_true_eq]
  intro x h
  rcases Set.mem_of_subset_of_mem (List.replicate_subset_singleton _ _) h
  · rfl
  · contradiction

-- todo: prove these 2 theorems to show that `ListBlank.toList` is correct
--theorem mk_truncateList_eq_mk (l : List Sym) :
--    ListBlank.mk (truncateList l) = ListBlank.mk l := sorry

--theorem toList_mk (lb : ListBlank Sym) : ListBlank.mk lb.toList = lb := sorry

end Turing.ListBlank

def toWord : List (Q ⊕ Sym) :=
  (c.2.left.toList.map Sum.inr).reverse ++
  Sum.inr c.2.head ::
  Sum.inl c.1 ::
  (c.2.right.toList.map Sum.inr)
