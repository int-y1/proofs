import Mathlib.Tactic.Ring
import BusyLean.BB62

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

notation c " ⊢ " c' => c [tm]⊢ c'
notation c " ⊢* " c' => c [tm]⊢* c'
notation c " ⊢⁺ " c' => c [tm]⊢⁺ c'

-- todo: move this elsewhere
macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [Turing.ListBlank.head_cons]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))

def A (a b c : Nat) :=
  (default <+ [(1 : Symbol)]^a << 0 <+ [(1 : Symbol), 0]^b << 0 <+ [(1 : Symbol), 1]^(c + 1))
    {{B}}> default

/-- 11^n <{A} ⊢* <{A} 10^n -/
lemma step_11A_A10 (l r : Side) (n : Nat) :
    ((l <+ [(1 : Symbol), 1]^n) <{{A}} r) ⊢* (l <{{A}} [(1 : Symbol), 0]^n +> r) := by
  revert l r
  induction' n with n ih <;> intros l r
  · finish
  rw [list_pow_add, Turing.ListBlank.append_assoc]
  refine stepStar_trans (ih _ _) ?_
  simp [(· ^ ·)]
  step; step; finish

/-- {B}> 10^n ⊢* 11^n {B}> -/
lemma step_B10_11B (l r : Side) (n : Nat) :
    (l {{B}}> [(1 : Symbol), 0]^n +> r) ⊢* ((l <+ [(1 : Symbol), 1]^n) {{B}}> r) := by
  revert l r
  induction' n with n ih <;> intros l r
  · finish
  rw [list_pow_add, Turing.ListBlank.append_assoc]
  refine stepStar_trans (ih _ _) ?_
  simp [(· ^ ·)]
  step; step; finish

/-- {F}> 10^n ⊢* 11^n {F}> -/
lemma step_F10_11F (l r : Side) (n : Nat) :
    (l {{F}}> [(1 : Symbol), 0]^n +> r) ⊢* ((l <+ [(1 : Symbol), 1]^n) {{F}}> r) := by
  revert l r
  induction' n with n ih <;> intros l r
  · finish
  rw [list_pow_add, Turing.ListBlank.append_assoc]
  refine stepStar_trans (ih _ _) ?_
  simp [(· ^ ·)]
  step; step; finish

/-- {C}> 10^n ⊢* 01^n {C}> -/
lemma step_C10_01C (l r : Side) (n : Nat) :
    (l {{C}}> [(1 : Symbol), 0]^n +> r) ⊢* ((l <+ [(1 : Symbol), 0]^n) {{C}}> r) := by
  revert l r
  induction' n with n ih <;> intros l r
  · finish
  rw [list_pow_add, Turing.ListBlank.append_assoc, ← list_pow_add]
  refine stepStar_trans (ih _ _) ?_
  simp [(· ^ ·)]
  step; step; finish

/-- A(a,b+2,c) ⊢* A(a,b,c+3) -/
theorem step_A_a_b2_c (a b c : Nat) : (A a (b + 2) c) ⊢* (A a b (c + 3)) := by
  simp only [A]
  step; step; step
  refine stepStar_trans (step_11A_A10 _ _ _) ?_
  step
  refine stepStar_trans (step_B10_11B _ _ _) ?_
  step; step; step
  refine stepStar_trans (step_11A_A10 _ _ _) ?_
  step
  simp_rw [add_comm b 2, (by ring : c + 3 + 1 = 2 + c + 2),
    list_pow_add, Turing.ListBlank.append_assoc]
  simp [(· ^ ·)]
  step; step; step; step
  refine stepStar_trans (step_B10_11B _ _ _) ?_
  step; step; step; step
  finish

/-- A(a+1,0,c) ⊢* A(a,c,2) -/
theorem step_A_a1_0_c (a c : Nat) : (A (a + 1) 0 c) ⊢* (A a c 2) := by
  simp only [A]
  step; step; step
  refine stepStar_trans (step_11A_A10 _ _ _) ?_
  step
  refine stepStar_trans (step_B10_11B _ _ _) ?_
  step; step; step
  refine stepStar_trans (step_11A_A10 _ _ _) ?_
  rw [(by simp [(· ^ ·)] : [(1 : Symbol), 0] ^ 0 = []),
    add_comm, list_pow_add, (by simp [(· ^ ·)] : [(1 : Symbol)] ^ 1 = [(1 : Symbol)])]
  simp_rw [Turing.ListBlank.append_assoc, Turing.ListBlank.append]
  step; step; step; step; step
  refine stepStar_trans (step_C10_01C _ _ _) ?_
  step; step; step; step; step; step; step; step; step
  rw [add_comm, list_pow_add, (by simp [(· ^ ·)] : [(1 : Symbol), 0] ^ 1 = [(1 : Symbol), 0])]
  simp_rw [Turing.ListBlank.append_assoc, Turing.ListBlank.append]
  step; step; step; step; step; step
  have h (s : Side) (n : Nat) :
      ([(1 : Symbol), 0]^(n + 1) +> s) = ([(1 : Symbol), 0]^n +> 1 >> 0 >> s) := by
    rw [list_pow_add, Turing.ListBlank.append_assoc]; rfl
  rw [← h]
  finish

/-- A(a+1,1,c) ⊢* A(a,c+4,0) -/
lemma step_A_a1_1_c_v1 (a c : Nat) : (A (a + 1) 1 c) ⊢* (A a (c + 4) 0) := by
  simp only [A]
  step; step; step
  refine stepStar_trans (step_11A_A10 _ _ _) ?_
  step
  refine stepStar_trans (step_B10_11B _ _ _) ?_
  step; step; step
  refine stepStar_trans (step_11A_A10 _ _ _) ?_
  rw [(by simp [(· ^ ·)] : [(1 : Symbol), 0] ^ 1 = [(1 : Symbol), 0]),
    add_comm, list_pow_add, (by simp [(· ^ ·)] : [(1 : Symbol)] ^ 1 = [(1 : Symbol)])]
  simp_rw [Turing.ListBlank.append_assoc, Turing.ListBlank.append]
  step; step; step; step; step
  refine stepStar_trans (step_B10_11B _ _ _) ?_
  step; step; step; step; step; step; step
  refine stepStar_trans (step_11A_A10 _ _ _) ?_
  step; step; step; step; step; step; step; step; step
  refine stepStar_trans (step_C10_01C _ _ _) ?_
  step; step; step; step; step
  --rw [add_comm, list_pow_add, (by simp [(· ^ ·)] : [(1 : Symbol), 0] ^ 1 = [(1 : Symbol), 0])]
  --simp_rw [Turing.ListBlank.append_assoc, Turing.ListBlank.append]
  have h (s : Side) (n : Nat) :
      ([(1 : Symbol), 0]^(n + 1) +> s) = ([(1 : Symbol), 0]^n +> 1 >> 0 >> s) := by
    rw [list_pow_add, Turing.ListBlank.append_assoc]; rfl
  rw [← h, ← h]
  simp [(· ^ ·)]
  finish

/-- A(a+1,1,c) ⊢* A(a,c,6) -/
theorem step_A_a1_1_c (a c : Nat) : (A (a + 1) 1 c) ⊢* (A a c 6) := by
  refine stepStar_trans (step_A_a1_1_c_v1 _ _) ?_
  refine stepStar_trans (step_A_a_b2_c _ _ _) ?_
  refine stepStar_trans (step_A_a_b2_c _ _ _) ?_
  finish

/-- A(0,0,c) halts -/
theorem step_A_0_0_c (c : Nat) : halts tm (A 0 0 c) := by
  refine' stepStar_halts
    (c₂ := ((default << 1 << 1 << 1 <+ [(1 : Symbol), 1]^(c + 1) << 1 << 1) {{F}}> default)) _
    (by exists 0, ((default << 1 << 1 << 1 <+ [(1 : Symbol), 1]^(c + 1) << 1 << 1) {{F}}> default))
  simp only [A]
  step; step; step
  refine stepStar_trans (step_11A_A10 _ _ _) ?_
  step
  refine stepStar_trans (step_B10_11B _ _ _) ?_
  step; step; step
  refine stepStar_trans (step_11A_A10 _ _ _) ?_
  rw [(by simp [(· ^ ·)] : [(1 : Symbol), 0] ^ 0 = []),
    (by simp [(· ^ ·)] : [(1 : Symbol)] ^ 0 = [])]
  simp_rw [Turing.ListBlank.append]
  step; step; step; step; step
  refine stepStar_trans (step_F10_11F _ _ _) ?_
  step; step; finish

/-- A(0,1,c) ⊢* A(2c+9,0,0) -/
theorem step_A_0_1_c (c : Nat) : (A 0 1 c) ⊢* (A (2 * c + 9) 0 0) := by
  simp only [A]
  step; step; step
  refine stepStar_trans (step_11A_A10 _ _ _) ?_
  step
  refine stepStar_trans (step_B10_11B _ _ _) ?_
  step; step; step
  refine stepStar_trans (step_11A_A10 _ _ _) ?_
  rw [(by simp [(· ^ ·)] : [(1 : Symbol), 0] ^ 0 = []),
    (by simp [(· ^ ·)] : [(1 : Symbol)] ^ 0 = []),
    (by simp [(· ^ ·)] : [(1 : Symbol), 0] ^ 1 = [(1 : Symbol), 0])]
  simp_rw [Turing.ListBlank.append]
  step; step; step; step; step
  refine stepStar_trans (step_B10_11B _ _ _) ?_
  step; step; step; step; step; step; step
  refine stepStar_trans (step_11A_A10 _ _ _) ?_
  step; step; step; step; step; step; step; step; step
  refine stepStar_trans (step_F10_11F _ _ _) ?_
  step; step; step; step; step; step; step; step; step; step
  have h (n : Nat) : [(1 : Symbol), 1]^n = [(1 : Symbol)]^(2 * n) := by
    induction' n with n ih
    · rfl
    simp_rw [mul_add, list_pow_add, ih]
    rfl
  rw [h, mul_add, (by ring : (2 * c + 9 = 2 + 2 * c + 7))]
  simp_rw [list_pow_add, Turing.ListBlank.append_assoc]
  simp [(· ^ ·)]
  finish

/-- c₀ ⊢* A(3,0,0) -/
theorem reach_3 : c₀ ⊢* (A 3 0 0) := by execute

/-- c₀ ⊢* A(25,0,0) -/
theorem reach_25 : c₀ ⊢* (A 25 0 0) := by
  refine stepStar_trans reach_3 ?_
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c _ _ _) ?_
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c _ _ _) ?_
  refine stepStar_trans (step_A_a_b2_c _ _ _) ?_
  refine stepStar_trans (step_A_0_1_c _) ?_
  finish

/-- A(a,b,c) ⊢* A(a,b%2,c+3*(b%2)) -/
theorem step_A_a_b2_c_fast (a b c : Nat) : (A a b c) ⊢* (A a (b % 2) (c + 3 * (b / 2))) := by
  match b with
  | 0 => finish
  | 1 => finish
  | b + 2 =>
    refine stepStar_trans (step_A_a_b2_c _ _ _) ?_
    refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_
    rw [Nat.add_mod_right, Nat.add_div_right _ (by decide)]
    ring_nf
    finish

/-- c₀ ⊢* A(227097,0,0) -/
theorem reach_227097 : c₀ ⊢* (A 227097 0 0) := by
  refine stepStar_trans reach_25 ?_
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_1_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_1_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_1_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_1_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_1_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_1_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_1_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_1_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_1_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_1_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_0_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_1_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_a1_1_c _ _) ?_
  refine stepStar_trans (step_A_a_b2_c_fast _ _ _) ?_; ring_nf
  refine stepStar_trans (step_A_0_1_c _) ?_
  finish

/-- This is a conjecture. -/
theorem halt : halts tm c₀ := by
  refine stepStar_halts reach_227097 ?_
  sorry
