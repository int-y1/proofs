import Mathlib.Tactic.Ring
import BusyLean.BB62
import BusyLean.TMAcceleration

/-!
# 1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE

https://wiki.bbchallenge.org/wiki/1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE

This file proves the forward rules of this TM, as shown in the wiki.
-/

section
open State
def tm : TM62 := fun ⟨q, s⟩ ↦
  match q, s with
  | A, 0 => some (1, R, B)  | A, 1 => some (0, L, D)
  | B, 0 => some (1, R, C)  | B, 1 => some (1, R, A)
  | C, 0 => some (1, L, D)  | C, 1 => some (0, R, B)
  | D, 0 => some (1, L, E)  | D, 1 => some (1, L, A)
  | E, 0 => some (1, R, F)  | E, 1 => some (0, R, C)
  | F, 0 => none            | F, 1 => some (1, R, E)
end section

open Symbol

local notation3:50 c:60 " ⊢ " c':60 => c [tm]⊢ c'
local notation3:50 c:60 " ⊢* " c':60 => c [tm]⊢* c'
local notation3:50 c:60 " ⊢⁺ " c':60 => c [tm]⊢⁺ c'

def A (a b c : Nat) := default <+ [S1]^a << 0 <+ [S1, S0]^b << 0 <+ [S1, S1]^(c + 1) {{B}}> default

/-- 11^n <{A} ⊢* <{A} 10^n -/
lemma step_11A_A10 (l r : Side) (n : Nat) :
    l <+ [S1, S1]^n <{{A}} r ⊢* l <{{A}} [S1, S0]^n +> r := by
  apply step_lq_ql_repeat
  intro l r
  simp; execute 2

/-- {B}> 10^n ⊢* 11^n {B}> -/
lemma step_B10_11B (l r : Side) (n : Nat) :
    l {{B}}> [S1, S0]^n +> r ⊢* l <+ [S1, S1]^n {{B}}> r := by
  apply step_ql_lq_repeat
  intro l r
  simp; execute 2

/-- {F}> 10^n ⊢* 11^n {F}> -/
lemma step_F10_11F (l r : Side) (n : Nat) :
    l {{F}}> [S1, S0]^n +> r ⊢* l <+ [S1, S1]^n {{F}}> r := by
  apply step_ql_lq_repeat
  intro l r
  simp; execute 2

/-- {C}> 10^n ⊢* 01^n {C}> -/
lemma step_C10_01C (l r : Side) (n : Nat) :
    l {{C}}> [S1, S0]^n +> r ⊢* l <+ [S1, S0]^n {{C}}> r := by
  apply step_ql_lq_repeat
  intro l r
  simp; execute 2

/-- A(a,b+2,c) ⊢* A(a,b,c+3) -/
theorem step_A_a_b2_c (a b c : Nat) : A a (b + 2) c ⊢* A a b (c + 3) := by
  simp only [A]
  step; step; step
  apply stepStar_trans (step_11A_A10 _ _ _)
  step
  apply stepStar_trans (step_B10_11B _ _ _)
  step; step; step
  apply stepStar_trans (step_11A_A10 _ _ _)
  step
  simp_rw [add_comm b 2, (by ring : c + 3 + 1 = 2 + c + 2),
    list_pow_add, Turing.ListBlank.append_assoc]
  simp [list_pow_two]
  step; step; step; step
  apply stepStar_trans (step_B10_11B _ _ _)
  execute 4

/-- A(a+1,0,c) ⊢* A(a,c,2) -/
theorem step_A_a1_0_c (a c : Nat) : A (a + 1) 0 c ⊢* A a c 2 := by
  simp only [A]
  step; step; step
  apply stepStar_trans (step_11A_A10 _ _ _)
  step
  apply stepStar_trans (step_B10_11B _ _ _)
  step; step; step
  apply stepStar_trans (step_11A_A10 _ _ _)
  rw [list_pow_zero, add_comm, list_pow_add, list_pow_one]
  simp_rw [Turing.ListBlank.append_assoc, Turing.ListBlank.append]
  step; step; step; step; step
  apply stepStar_trans (step_C10_01C _ _ _)
  step; step; step; step; step; step; step; step; step
  rw [add_comm, list_pow_add, list_pow_one]
  simp_rw [Turing.ListBlank.append_assoc, Turing.ListBlank.append]
  step; step; step; step; step; step
  rw [← list2_append_eq]
  finish

/-- A(a+1,1,c) ⊢* A(a,c+4,0) -/
lemma step_A_a1_1_c_v1 (a c : Nat) : A (a + 1) 1 c ⊢* A a (c + 4) 0 := by
  simp only [A]
  step; step; step
  apply stepStar_trans (step_11A_A10 _ _ _)
  step
  apply stepStar_trans (step_B10_11B _ _ _)
  step; step; step
  apply stepStar_trans (step_11A_A10 _ _ _)
  rw [list_pow_one, add_comm, list_pow_add, list_pow_one]
  simp_rw [Turing.ListBlank.append_assoc, Turing.ListBlank.append]
  step; step; step; step; step
  apply stepStar_trans (step_B10_11B _ _ _)
  step; step; step; step; step; step; step
  apply stepStar_trans (step_11A_A10 _ _ _)
  step; step; step; step; step; step; step; step; step
  apply stepStar_trans (step_C10_01C _ _ _)
  step; step; step; step; step
  rw [← list2_append_eq, ← list2_append_eq]
  simp [(· ^ ·)]
  finish

/-- A(a+1,1,c) ⊢* A(a,c,6) -/
theorem step_A_a1_1_c (a c : Nat) : A (a + 1) 1 c ⊢* A a c 6 := by
  apply stepStar_trans (step_A_a1_1_c_v1 _ _)
  apply stepStar_trans (step_A_a_b2_c _ _ _)
  apply stepStar_trans (step_A_a_b2_c _ _ _)
  finish

/-- A(0,0,c) halts -/
theorem step_A_0_0_c (c : Nat) : halts tm (A 0 0 c) := by
  refine' stepStar_halts
    (c₂ := default << 1 << 1 << 1 <+ [S1, S1]^(c + 1) << 1 << 1 {{F}}> default) _
    (by exists 0, default << 1 << 1 << 1 <+ [S1, S1]^(c + 1) << 1 << 1 {{F}}> default)
  simp only [A]
  step; step; step
  apply stepStar_trans (step_11A_A10 _ _ _)
  step
  apply stepStar_trans (step_B10_11B _ _ _)
  step; step; step
  apply stepStar_trans (step_11A_A10 _ _ _)
  rw [list_pow_zero, list_pow_zero]
  simp_rw [Turing.ListBlank.append]
  step; step; step; step; step
  apply stepStar_trans (step_F10_11F _ _ _)
  execute 2

/-- A(0,1,c) ⊢* A(2c+9,0,0) -/
theorem step_A_0_1_c (c : Nat) : A 0 1 c ⊢* A (2 * c + 9) 0 0 := by
  simp only [A]
  step; step; step
  apply stepStar_trans (step_11A_A10 _ _ _)
  step
  apply stepStar_trans (step_B10_11B _ _ _)
  step; step; step
  apply stepStar_trans (step_11A_A10 _ _ _)
  rw [list_pow_zero, list_pow_zero, list_pow_one]
  simp_rw [Turing.ListBlank.append]
  step; step; step; step; step
  apply stepStar_trans (step_B10_11B _ _ _)
  step; step; step; step; step; step; step
  apply stepStar_trans (step_11A_A10 _ _ _)
  step; step; step; step; step; step; step; step; step
  apply stepStar_trans (step_F10_11F _ _ _)
  step; step; step; step; step; step; step; step; step; step
  have h (n : Nat) : [S1, S1]^n = [S1]^(2 * n) := by
    rw [list_pow_mul]; rfl
  rw [h, mul_add, (by ring : (2 * c + 9 = 2 + 2 * c + 7))]
  simp_rw [list_pow_add, Turing.ListBlank.append_assoc]
  simp [(· ^ ·)]
  finish

/-- c₀ ⊢* A(3,0,0) -/
theorem reach_3 : c₀ ⊢* A 3 0 0 := by execute 17

/-- c₀ ⊢* A(25,0,0) -/
theorem reach_25 : c₀ ⊢* A 25 0 0 := by
  apply stepStar_trans reach_3
  apply stepStar_trans (step_A_a1_0_c _ _)
  apply stepStar_trans (step_A_a1_0_c _ _)
  apply stepStar_trans (step_A_a_b2_c _ _ _)
  apply stepStar_trans (step_A_a1_0_c _ _)
  apply stepStar_trans (step_A_a_b2_c _ _ _)
  apply stepStar_trans (step_A_a_b2_c _ _ _)
  apply stepStar_trans (step_A_0_1_c _)
  finish

/-- A(a,b,c) ⊢* A(a,b%2,c+3*(b/2)) -/
lemma step_A_a_b2_c_fast (a b c : Nat) : A a b c ⊢* A a (b % 2) (c + 3 * (b / 2)) := by
  match b with
  | 0 => finish
  | 1 => finish
  | b + 2 =>
    apply stepStar_trans (step_A_a_b2_c _ _ _)
    apply stepStar_trans (step_A_a_b2_c_fast _ _ _)
    rw [Nat.add_mod_right, Nat.add_div_right _ (by decide)]
    ring_nf
    finish

/-- A(a+1,0,c) ⊢* A(a,c%2,2+3*(c/2)) -/
theorem step_A_a1_0_c_fast (a c : Nat) : A (a + 1) 0 c ⊢* A a (c % 2) (2 + 3 * (c / 2)) := by
  apply stepStar_trans (step_A_a1_0_c _ _)
  apply stepStar_trans (step_A_a_b2_c_fast _ _ _)
  finish

/-- A(a+1,1,c) ⊢* A(a,c%2,6+3*(c/2)) -/
theorem step_A_a1_1_c_fast (a c : Nat) : A (a + 1) 1 c ⊢* A a (c % 2) (6 + 3 * (c / 2)) := by
  apply stepStar_trans (step_A_a1_1_c _ _)
  apply stepStar_trans (step_A_a_b2_c_fast _ _ _)
  finish

/-- A(a+1,b,c) ⊢* A(a,c%2,2+4*b+3*(c/2)), where b < 2 -/
theorem step_A_a1_01_c_fast (a b c : Nat) (hb : b < 2) :
    A (a + 1) b c ⊢* A a (c % 2) (2 + 4 * b + 3 * (c / 2)) := by
  match b with
  | 0 => apply step_A_a1_0_c_fast
  | 1 => apply step_A_a1_1_c_fast
  | b + 2 => simp at hb

/-- c₀ ⊢* A(227097,0,0) -/
theorem reach_227097 : c₀ ⊢* A 227097 0 0 := by
  apply stepStar_trans reach_25
  -- alternate between `step_A_a1_0_c_fast` and `step_A_a1_1_c_fast` randomly
  iterate 25 apply stepStar_trans (step_A_a1_01_c_fast _ _ _ (by decide)); ring_nf
  apply stepStar_trans (step_A_0_1_c _)
  finish

/-- This is a conjecture. -/
theorem halt : halts tm c₀ := by
  apply stepStar_halts reach_227097
  sorry
