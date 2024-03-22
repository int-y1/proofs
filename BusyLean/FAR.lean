import Mathlib.Computability.TuringMachine
import Mathlib.Data.List.DropRight
import BusyLean.TM
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

--theorem mk_truncateList_eq_mk (l : List Sym) :
--    ListBlank.mk (truncateList l) = ListBlank.mk l := sorry

-- todo: prove this theorem to show that `ListBlank.toList` is the inverse of `ListBlank.mk`
--theorem toList_mk (lb : ListBlank Sym) : ListBlank.mk lb.toList = lb := sorry

end Turing.ListBlank

/-- Word-representation of a configuration. -/
def toWord : List (Q ⊕ Sym) :=
  (c.2.left.tail.toList.map .inr).reverse ++
  .inr c.2.left.head ::
  .inl c.1 ::
  .inr c.2.head ::
  (c.2.right.toList.map .inr)

--#eval toWord (Q := Fin 5) (Sym := Fin 2) (default {{4}}> 0 >> 0 >> 1 >> 1 >> default)

/-- A nondeterministic finite automaton with `n` states, represented using `n × n` boolean matrices
and `1 × n` boolean vectors. -/
structure BooleanNFA {n : ℕ} where
  /-- Initial states of the NFA. -/
  q₀ : Matrix (Fin 1) (Fin n) Two
  /-- Transition matrices of the NFA. If `T γ i j = 1`, then the NFA transitions from `i` to `j`
  when reading `γ`. -/
  T : Q ⊕ Sym → Matrix (Fin n) (Fin n) Two
  /-- Accepting states of the NFA. -/
  a : Matrix (Fin 1) (Fin n) Two

open Matrix

/-- todo: statement is wrong. fix the statement. -/
theorem foo {n : ℕ} (tm : @TM Q Sym) (b : @BooleanNFA Q Sym n) (s : Matrix (Fin 1) (Fin n) Two)
    (h₁ : b.q₀ * (b.T (.inr default)) = b.q₀)
    (h₂ : (b.T (.inr default)) * b.aᵀ = b.aᵀ)
    (h₃ : s * b.aᵀ = 1)
    (h₄ : ∀ i : Sym, s * (b.T (.inr i)) ≥ s)
    (h₅ : ∀ f r, match tm ⟨f, r⟩ with
      | none => True -- todo: replace `True` with the actual condition
      | some (w, L, t) => ∀ i : Sym,
        b.T (.inr i) * b.T (.inl f) * b.T (.inr r) ≥ b.T (.inl t) * b.T (.inr i) * b.T (.inr w)
      | some (w, R, t) => b.T (.inl f) * b.T (.inr r) ≥ b.T (.inr w) * b.T (.inl t)
    )
    (h₆ : b.q₀ * b.T (.inl default) * b.aᵀ = 0) : True := by
  trivial
