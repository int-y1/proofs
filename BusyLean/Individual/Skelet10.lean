import Mathlib.Tactic.Ring
import BusyLean.BB52

/-!
# Skelet #10

Original source: https://github.com/meithecatte/busycoq/blob/master/verify/Skelet10.v
-/

section
open State
def tm : TM52 := fun ⟨q, s⟩ ↦
  match q, s with
  | A, 0 => some (1, R, B)  | A, 1 => some (0, R, A)
  | B, 0 => some (0, L, C)  | B, 1 => some (1, R, A)
  | C, 0 => some (1, R, E)  | C, 1 => some (1, L, D)
  | D, 0 => some (1, L, C)  | D, 1 => some (0, L, D)
  | E, 0 => none            | E, 1 => some (0, R, B)
end section

local notation3:50 c:60 " ⊢ " c':60 => c [tm]⊢ c'
local notation3:50 c:60 " ⊢* " c':60 => c [tm]⊢* c'
local notation3:50 c:60 " ⊢⁺ " c':60 => c [tm]⊢⁺ c'

inductive Dorf
  | zend : Dorf
  | zO : Dorf → Dorf
  | zIO : Dorf → Dorf
open Dorf

/-- Note: We don't actually need to define `val` for the proof to go
through. It's just useful to sanity-check the definition. -/
def val' (n : Dorf) (prev cur : ℕ) : ℕ :=
  match n with
  | zend => 0
  | zO n' => val' n' cur (cur+prev)
  | zIO n' => cur + val' n' (cur+prev) (cur+prev+cur)

def val (n : Dorf) : ℕ := val' n 1 1

example : val (zO (zO (zIO (zIO zend)))) = 11 := rfl

def zI (n : Dorf) : Dorf :=
  match n with
  | zend => zIO zend
  | zO n' => zIO n'
  | zIO n' => zO (zO (zI n'))

def incr (n : Dorf) : Dorf :=
  match n with
  | zend => zIO zend
  | zO n' => zI n'
  | zIO n' => zO (zI n')

lemma zI_val' (n : Dorf) (prev cur : ℕ) : val' (zI n) prev cur = cur + val' n cur (cur + prev) := by
  match n with
  | zend => rfl
  | zO n' => rfl
  | zIO n' => simp_rw [zI, val', zI_val']; ring

lemma incr_val (n : Dorf) : val (incr n) = (val n)+1 := by
  match n with
  | zend => rfl
  | zO n' => simp_rw [val, incr, zI_val', val', add_comm]
  | zIO n' => simp_rw [val, incr, val', zI_val']; ring

/-- Right Side Counter -/
def Z (n : Dorf) : Side :=
  match n with
  | zend => default
  | zO n' => (0 : Symbol) >> Z n'
  | zIO n' => 1 >> 0 >> Z n'

-- todo: move this elsewhere
macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [Turing.ListBlank.head_cons]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))

lemma incr_right (n : Dorf) (l : Side) : l << 1 {{B}}> Z n ⊢* l <{{D}} Z (zI n) := by
  revert l; induction' n with _ _ _ IH <;> intro l
  · execute
  · simp_rw [Z]
    execute
  · simp_rw [Z]
    execute
    apply stepStar_trans (IH _)
    execute

/-- Left Side Counter -/
def T (n : Dorf) : Side :=
  match n with
  | zend => default
  | zO n' => T n' << 0 << 0
  | zIO n' => T n' << 1 << 0 << 1 << 0

/-- `L` was already taken, use `L'` instead -/
def L' (n : Dorf) : Side :=
  match n with
  | zend => default
  | zO n' => T n'
  | zIO n' => T n' << 1 << 0

lemma incr_left (n : Dorf) (r : Side) : T n <{{D}} 1 >> 1 >> r ⊢* T (zI n) {{A}}> r := by
  revert r; induction' n with _ _ _ IH <;> intro l
  · execute
  · simp_rw [T]
    execute
  · simp_rw [T]
    execute
    apply stepStar_trans (IH _)
    execute

/-- Complete Behavior -/
def D (n : Dorf) := L' n <{{D}} Z (incr n)

lemma incr_D (n : Dorf) : D n ⊢⁺ D (incr n) := by
  unfold D
  cases' n with n n
  · execute
  · cases' n with n n
    · execute
    · simp only [Z, L', T, incr, zI]
      execute
      apply stepStar_trans (incr_right _ _)
      execute
    · simp only [Z, L', T, incr, zI]
      execute
      apply stepStar_trans (incr_left _ _)
      execute
  · simp only [Z, L', incr]
    execute
    apply stepStar_trans (incr_left _ _)
    execute
    apply stepStar_trans (incr_right _ _)
    execute

theorem nonhalt : ¬halts tm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := D zend) (by execute)
  apply progress_nonhalt_simple D
  exact fun n ↦ ⟨incr n, incr_D n⟩
