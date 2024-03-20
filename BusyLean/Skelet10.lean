import Mathlib.Tactic.Ring
import BusyLean.BB52

/-!
# Skelet #10

Original source: https://github.com/meithecatte/busycoq/blob/master/verify/Skelet10.v
-/

variable (Q := State)
variable (Sym := Symbol)

open State

def tm : TM := fun ⟨q, s⟩ ↦
  match q, s with
  | A, 0 => some (1, R, B)  | A, 1 => some (0, R, A)
  | B, 0 => some (0, L, C)  | B, 1 => some (1, R, A)
  | C, 0 => some (1, R, E)  | C, 1 => some (1, L, D)
  | D, 0 => some (1, L, C)  | D, 1 => some (0, L, D)
  | E, 0 => none            | E, 1 => some (0, R, B)

notation c " ⊢ " c' => c [tm]⊢ c'
notation c " ⊢* " c' => c [tm]⊢* c'
notation c " ⊢⁺ " c' => c [tm]⊢⁺ c'

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

lemma incr_right (n : Dorf) (l : Side) : ((l << 1) {{B}}> Z n) ⊢* l <{{D}} Z (zI n) := by
  induction n
  sorry
