import Mathlib.Tactic.Ring
import BusyLean.BB62
import BusyLean.TMAcceleration

/-!
# 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---

Define `A(n,ls) := 0^inf <F 1^n 0 ls 0^inf`. This file proves the following results:

* `A(9,nil)` is reached.

-/

section
open State
def tm : TM62 := fun ⟨q, s⟩ ↦
  match q, s with
  | A, 0 => some (1, R, B)  | A, 1 => some (0, R, E)
  | B, 0 => some (1, L, C)  | B, 1 => some (0, R, A)
  | C, 0 => some (1, L, A)  | C, 1 => some (1, L, D)
  | D, 0 => some (1, L, C)  | D, 1 => some (1, L, F)
  | E, 0 => some (0, L, C)  | E, 1 => some (0, L, B)
  | F, 0 => some (1, L, E)  | F, 1 => none
end section

open Symbol

local notation3:50 c:60 " ⊢ " c':60 => c [tm]⊢ c'
local notation3:50 c:60 " ⊢* " c':60 => c [tm]⊢* c'
local notation3:50 c:60 " ⊢⁺ " c':60 => c [tm]⊢⁺ c'

def A (n : Nat) (ls : List Symbol) := default <{{F}} [S1]^n +> ls +> default

/-- c₀ ⊢* A(9,nil) -/
theorem reach_9_nil : c₀ ⊢* A 9 [] := by execute 36

/-- 0^∞ 101001 <{E} r ⊢* 0^∞ 11010101 {B}> r -/
lemma step_101001E_11010101B (r : Side) :
    default << 1 << 0 << 1 << 0 << 0 << 1 <{{E}} r ⊢*
    default << 1 << 1 <+ [S1, S0]^3 {{B}}> r := by execute 23

/-- l 10^n <{C} r ⊢* l <{C} 10^n r -/
lemma step_10C_C10 (l r : Side) (n : Nat) :
    l <+ [S0, S1]^n <{{C}} r ⊢* l <{{C}} [S1, S0]^n +> r := by
  apply step_lq_ql_repeat
  intro l r
  simp; execute 4

/-- l 01^n <{C} r ⊢* l <{C} 11^n r -/
lemma step_01C_C11 (l r : Side) (n : Nat) :
    l <+ [S1, S0]^n <{{C}} r ⊢* l <{{C}} [S1, S1]^n +> r := by
  apply step_lq_ql_repeat
  intro l r
  simp; execute 2

/-- l {B}> 10^n r ⊢* l 01^n {B}> r -/
lemma step_B10_01B (l r : Side) (n : Nat) :
    l {{B}}> [S1, S0]^n +> r ⊢* l <+ [S1, S0]^n {{B}}> r := by
  apply step_ql_lq_repeat
  intro l r
  simp; execute 2

/-- 0^∞ 11 01^n {B}> 111 r ⊢* 0^∞ 11 01^(n+4) {B}> r -/
lemma step_1101B111_1101B (r : Side) (n : Nat) :
    default << 1 << 1 <+ [S1, S0]^n {{B}}> 1 >> 1 >> 1 >> r ⊢*
    default << 1 << 1 <+ [S1, S0]^(n+4) {{B}}> r := by
  step
  rw [← list2_rotate, ← list2_append_eq]
  step; step; step
  apply stepStar_trans (step_10C_C10 _ _ _)
  iterate 18 step
  simp_rw [← list2_append_eq, ← list2_append_eq']
  step
  apply stepStar_trans (step_B10_01B _ _ _)
  finish

/-- 0^∞ 11 01^n {B}> 111^m r ⊢* 0^∞ 11 01^(n+4*m) {B}> r -/
lemma step_1101B111_1101B_repeat (r : Side) (n m : Nat) :
    default << 1 << 1 <+ [S1, S0]^n {{B}}> [S1]^(3*m) +> r ⊢*
    default << 1 << 1 <+ [S1, S0]^(n+4*m) {{B}}> r := by
  revert r
  induction' m with m ih <;> intro r
  · finish
  rw [mul_add, mul_add, list_pow_add, Turing.ListBlank.append_assoc]
  apply stepStar_trans (ih _)
  apply stepStar_trans (step_1101B111_1101B _ _)
  finish

/-- A(3n+2,ls) ⊢* 0^∞ 11 01^(4n+3) {B}> ls 0^∞ -/
lemma step_An2_1101B (n : Nat) (ls : List Symbol) :
    A (3*n+2) ls ⊢* default << 1 << 1 <+ [S1, S0]^(4*n+3) {{B}}> ls +> default := by
  rw [A, list1_append_eq', list1_append_eq', add_comm]
  iterate 8 step
  apply stepStar_trans (step_101001E_11010101B _)
  apply stepStar_trans (step_1101B111_1101B_repeat _ _ _)
  finish

/-- A(3n+3,ls) ⊢* 0^∞ 11 01^(4n+3) 0 {A}> ls 0^∞ -/
lemma step_An3_11010A (n : Nat) (ls : List Symbol) :
    A (3*n+3) ls ⊢* default << 1 << 1 <+ [S1, S0]^(4*n+3) << 0 {{A}}> ls +> default := by
  rw [A, list1_append_eq', list1_append_eq', list1_append_eq, add_comm]
  iterate 8 step
  apply stepStar_trans (step_101001E_11010101B _)
  apply stepStar_trans (step_1101B111_1101B_repeat _ _ _)
  execute 1

/-- A(3n+4,ls) ⊢* 0^∞ 11 01^(4n+3) 00 {E}> ls 0^∞ -/
lemma step_An4_110100E (n : Nat) (ls : List Symbol) :
    A (3*n+4) ls ⊢* default << 1 << 1 <+ [S1, S0]^(4*n+3) << 0 << 0 {{E}}> ls +> default := by
  rw [A, list1_append_eq', list1_append_eq', list1_append_eq, list1_append_eq, add_comm]
  iterate 8 step
  apply stepStar_trans (step_101001E_11010101B _)
  apply stepStar_trans (step_1101B111_1101B_repeat _ _ _)
  execute 2

theorem Nat.mod_three_eq_or : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 :=
  match n % 3, n.mod_lt zero_lt_three with
  | 0, _ | 1, _ | 2, _ => by trivial

/-- Do cases on `A(n,ls)`. -/
lemma step_An_1101 (n : Nat) (ls : List Symbol) (hn : n ≥ 4) :
    A n ls ⊢* ([
      default << 1 << 1 <+ [S1, S0]^(4*(n/3)-1) << 0 {{A}}> ls +> default,
      default << 1 << 1 <+ [S1, S0]^(4*(n/3)-1) << 0 << 0 {{E}}> ls +> default,
      default << 1 << 1 <+ [S1, S0]^(4*(n/3)+3) {{B}}> ls +> default
    ][n % 3]'(n.mod_lt zero_lt_three)) := by
  nth_rw 1 [← n.div_add_mod 3]
  rcases n.mod_three_eq_or with h | h | h <;>
    simp only [h, List.getElem_cons_succ, List.getElem_cons_zero]
  · have hn3 : n/3 ≥ 1 := (Nat.one_le_div_iff (zero_lt_three)).2 (le_trans (by decide) hn)
    rw [← Nat.sub_add_cancel hn3, mul_add]
    apply stepStar_trans (step_An3_11010A _ _)
    finish
  · have hn3 : n/3 ≥ 1 := (Nat.one_le_div_iff (zero_lt_three)).2 (le_trans (by decide) hn)
    rw [← Nat.sub_add_cancel hn3, mul_add]
    apply stepStar_trans (step_An4_110100E _ _)
    finish
  · apply stepStar_trans (step_An2_1101B _ _)
    finish

/-- Needed for A_step. -/
lemma list11_eq_list1 (n : Nat) : [S1, S1]^n = [S1]^(2*n) := by
  rw [list_pow_mul]; rfl

/-- Needed for A_step. -/
lemma default_tail : (default : Turing.ListBlank Symbol).tail = default := rfl

/-- Needed for A_step. -/
lemma nil_append_default : ([] : List Symbol) +> default = default := rfl

macro "A_step" n:num : tactic => `(tactic| (
  apply stepStar_trans (step_An_1101 _ _ (by decide))
  simp_rw [List.getElem_cons_succ, List.getElem_cons_zero]
  simp only [Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
  rw [list2_append_eq', list2_append_eq']
  simp_rw [Turing.ListBlank.append]
  iterate $n step
  apply stepStar_trans (step_01C_C11 _ _ _)
  step
  step
  simp_rw [list11_eq_list1 _, Nat.reduceMul, ← list1_append_eq, ← list1_append_eq', Nat.reduceAdd]
  repeat' (nth_rw 2 [default_tail])
  nth_rw 3 [← nil_append_default]
  repeat' rw [← Turing.ListBlank.append]
  rw [← A]))

macro "stepHalt" : tactic => `(tactic| (
  apply step_halts rfl
  simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]))

set_option maxHeartbeats 1000000 in
/-- This takes a while to compute. It's pretty unoptimized. -/
lemma halts_A1975700577069254261393123959451562008800234946348086 :
    halts tm (A 1975700577069254261393123959451562008800234946348086 []) := by
  apply stepStar_halts (c₂ := A 7488166283129708930486796847462680979065226437987146331898837006603604720521272903526417758309106 [0, 1, 0, 1, 1, 0, 1, 1])
  · A_step 13
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 17
    A_step 21
    A_step 5
    A_step 27
    A_step 35
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 5
    A_step 31
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 17
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 21
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 5
    A_step 31
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 21
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 27
    A_step 39
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 5
    A_step 31
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 17
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 21
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 5
    A_step 31
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 17
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 21
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    A_step 5
    A_step 21
    A_step 5
    finish
  apply stepStar_halts (step_An_1101 _ _ (by decide))
  simp_rw [List.getElem_cons_succ, List.getElem_cons_zero]
  simp only [Nat.reduceDiv, Nat.reduceMul]
  rw [list2_append_eq', list2_append_eq']
  simp_rw [Turing.ListBlank.append]
  iterate 113 stepHalt
  exists 0
  simp_rw [haltsIn, stepNat, Nat.repeat, Option.some.injEq, exists_eq_left']
  rfl
