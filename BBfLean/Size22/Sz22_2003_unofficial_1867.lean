import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1867: [9/35, 25/33, 14/3, 11/7, 21/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  2  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1867

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem d_to_e : ∀ k d, ⟨a, 0, 0, d + k, 0⟩ [fm]⊢* ⟨a, 0, 0, d, k⟩ := by
  intro k; induction k with
  | zero => intro d; exists 0
  | succ k ih =>
    intro d; rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (d + 1)); step fm; ring_nf; finish

theorem loop_c0 : ⟨a + 1, 0, 0, 0, e + 3⟩ [fm]⊢* ⟨a, 0, 5, 0, e⟩ := by execute fm 5
theorem loop_cpos : ⟨a + 1, 0, c + 1, 0, e + 3⟩ [fm]⊢* ⟨a, 0, c + 6, 0, e⟩ := by execute fm 5

theorem loop_iter_gen : ∀ k a c, ⟨a + k, 0, c + 1, 0, 3 * k + r⟩ [fm]⊢* ⟨a, 0, c + 5 * k + 1, 0, r⟩ := by
  intro k; induction k with
  | zero => intro a c; simp; exists 0
  | succ k ih =>
    intro a c
    rw [show a + (k + 1) = a + k + 1 from by ring,
        show 3 * (k + 1) + r = (3 * k + r) + 3 from by ring,
        show c + 5 * (k + 1) + 1 = c + 5 + 5 * k + 1 from by ring]
    apply stepStar_trans (loop_cpos (a := a + k) (c := c) (e := 3 * k + r))
    rw [show c + 6 = c + 5 + 1 from by ring]; exact ih a (c + 5)

theorem drain : ∀ q a, ⟨a + q + 1, 0, 0, 0, 3 * (q + 1) + r⟩ [fm]⊢* ⟨a, 0, 5 * (q + 1), 0, r⟩ := by
  intro q a
  rw [show 3 * (q + 1) + r = (3 * q + r) + 3 from by ring,
      show a + q + 1 = (a + q) + 1 from by ring]
  apply stepStar_trans (loop_c0 (a := a + q) (e := 3 * q + r))
  rw [show (5 : ℕ) = 4 + 1 from rfl, show 5 * (q + 1) = 4 + 5 * q + 1 from by ring]
  exact loop_iter_gen q a 4

theorem rem_r1 : ⟨a + 1, 0, c + 1, 0, 1⟩ [fm]⊢* ⟨a, 2, c + 2, 0, 0⟩ := by execute fm 3
theorem rem_r2_cpos : ⟨a + 1, 0, c + 1, 0, 2⟩ [fm]⊢* ⟨a, 1, c + 4, 0, 0⟩ := by execute fm 4
theorem rem_r2_c0 : ⟨a + 1, 0, 0, 0, 2⟩ [fm]⊢* ⟨a, 1, 3, 0, 0⟩ := by execute fm 4
theorem open_b0 : ⟨a + 1, 0, c + 1, 0, 0⟩ [fm]⊢* ⟨a, 3, c, 0, 0⟩ := by execute fm 2

theorem spiral : ∀ k a b, ⟨a, b + 1, k, 0, 0⟩ [fm]⊢* ⟨a + k, b + k + 1, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; simp; exists 0
  | succ k ih =>
    intro a b; step fm; step fm
    rw [show a + (k + 1) = a + 1 + k from by ring,
        show b + (k + 1) + 1 = b + 1 + k + 1 from by ring]
    exact ih (a + 1) (b + 1)

theorem r3_chain : ∀ k a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; exists 0
  | succ k ih =>
    intro a d; step fm
    rw [show a + (k + 1) = a + 1 + k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    exact ih (a + 1) (d + 1)

theorem end_phase : ∀ C, ⟨a, B + 1, C, 0, 0⟩ [fm]⊢* ⟨a + B + 2 * C + 1, 0, 0, 0, B + C + 1⟩ := by
  intro C
  apply stepStar_trans (spiral C a B)
  apply stepStar_trans (r3_chain (B + C + 1) (a + C) 0)
  rw [show 0 + (B + C + 1) = 0 + (B + C + 1) from rfl]
  apply stepStar_trans (d_to_e (B + C + 1) 0 (a := a + C + (B + C + 1)))
  rw [show a + C + (B + C + 1) = a + B + 2 * C + 1 from by ring]; finish

-- All transitions use the pattern: first step is R5 via step_stepStar_stepPlus,
-- then rem or drain via stepStar_trans, then end_phase via stepStar_trans.
-- The R5 step provides the ⊢⁺.

-- e=2: (a+2, 0, 0, 0, 2) ⊢⁺ (a+8, 0, 0, 0, 4)
-- R5: (a+1, 1, 0, 1, 2). Then R2: (a+1, 0, 2, 1, 1). R1: (a+1, 2, 1, 0, 1).
-- R2: (a+1, 1, 3, 0, 0). = rem_r2_c0 output + 1 step.
-- Actually rem_r2_c0: (a'+1, 0, 0, 0, 2) ->* (a', 1, 3, 0, 0).
-- So from (a+2, 0, 0, 0, 2), rem_r2_c0 (a':=a+1): ->* (a+1, 1, 3, 0, 0).
-- Then end_phase(C=3, B=0): (a+1, 0+1, 3, 0, 0) ->* (a+1+0+6+1, 0, 0, 0, 0+3+1) = (a+8, 0, 0, 0, 4).
-- Need ⊢⁺: use stepStar_stepPlus with c₁ ≠ c₂.
theorem trans_e2 : ⟨a + 2, 0, 0, 0, 2⟩ [fm]⊢⁺ ⟨a + 8, 0, 0, 0, 4⟩ := by
  rw [show a + 2 = (a + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (end_phase 3 (a := a + 1) (B := 0))
  rw [show a + 1 + 0 + 2 * 3 + 1 = a + 8 from by ring,
      show 0 + 3 + 1 = 4 from by ring]; finish

-- e = 3*(q+1): (a+q+2, 0, 0, 0, 3*(q+1)) ⊢⁺ (a+10*q+11, 0, 0, 0, 5*q+7)
theorem trans_mod0 : ∀ q a, ⟨a + q + 2, 0, 0, 0, 3 * (q + 1)⟩ [fm]⊢⁺
    ⟨a + 10 * q + 11, 0, 0, 0, 5 * q + 7⟩ := by
  intro q a
  rw [show 3 * (q + 1) = 3 * (q + 1) + 0 from by ring,
      show a + q + 2 = (a + 1) + q + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (drain q (a + 1) (r := 0))
  rw [show 5 * (q + 1) = (5 * q + 4) + 1 from by ring]
  -- at (a+1, 0, (5*q+4)+1, 0, 0). open_b0 gives (a, 3, 5*q+4, 0, 0).
  -- Then R3+R1 gives (a+1, 4, 5*q+3, 0, 0). end_phase continues.
  step fm; step fm  -- open_b0: R5, R1
  step fm; step fm  -- R3, R1
  apply stepStar_trans (end_phase (5 * q + 3) (a := a + 1) (B := 3))
  rw [show a + 1 + 3 + 2 * (5 * q + 3) + 1 = a + 10 * q + 11 from by ring,
      show 3 + (5 * q + 3) + 1 = 5 * q + 7 from by ring]; finish

-- e = 3*(q'+1)+1: (a+q'+3, 0, 0, 0, 3*(q'+1)+1) ⊢⁺ (a+10*q'+15, 0, 0, 0, 5*q'+8)
theorem trans_mod1 : ∀ q' a, ⟨a + q' + 3, 0, 0, 0, 3 * (q' + 1) + 1⟩ [fm]⊢⁺
    ⟨a + 10 * q' + 15, 0, 0, 0, 5 * q' + 8⟩ := by
  intro q' a
  rw [show a + q' + 3 = (a + 2) + q' + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (drain q' (a + 2) (r := 1))
  rw [show 5 * (q' + 1) = (5 * q' + 4) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (rem_r1 (a := a + 1) (c := 5 * q' + 4))
  rw [show 5 * q' + 4 + 2 = 5 * q' + 6 from by ring]
  step fm; step fm
  apply stepStar_trans (end_phase (5 * q' + 5) (a := a + 2) (B := 2))
  rw [show a + 2 + 2 + 2 * (5 * q' + 5) + 1 = a + 10 * q' + 15 from by ring,
      show 2 + (5 * q' + 5) + 1 = 5 * q' + 8 from by ring]; finish

-- e = 3*(q'+1)+2: (a+q'+3, 0, 0, 0, 3*(q'+1)+2) ⊢⁺ (a+10*q'+18, 0, 0, 0, 5*q'+9)
theorem trans_mod2 : ∀ q' a, ⟨a + q' + 3, 0, 0, 0, 3 * (q' + 1) + 2⟩ [fm]⊢⁺
    ⟨a + 10 * q' + 18, 0, 0, 0, 5 * q' + 9⟩ := by
  intro q' a
  rw [show a + q' + 3 = (a + 2) + q' + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (drain q' (a + 2) (r := 2))
  rw [show 5 * (q' + 1) = (5 * q' + 4) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (rem_r2_cpos (a := a + 1) (c := 5 * q' + 4))
  rw [show 5 * q' + 4 + 4 = 5 * q' + 8 from by ring]
  step fm; step fm
  apply stepStar_trans (end_phase (5 * q' + 7) (a := a + 2) (B := 1))
  rw [show a + 2 + 1 + 2 * (5 * q' + 7) + 1 = a + 10 * q' + 18 from by ring,
      show 1 + (5 * q' + 7) + 1 = 5 * q' + 9 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 0, 4⟩) (by execute fm 22)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ e + 1 ∧ e ≥ 2)
  · intro c ⟨A, E, hq, ha, he⟩; subst hq
    rcases Nat.lt_or_ge E 3 with he3 | he3
    · have hE : E = 2 := by omega
      subst hE
      exact ⟨⟨A + 6, 0, 0, 0, 4⟩,
        ⟨A + 6, 4, rfl, by omega, by omega⟩,
        by rw [show A = (A - 2) + 2 from by omega,
               show (A - 2) + 2 + 6 = (A - 2) + 8 from by ring]; exact trans_e2⟩
    · rcases Nat.lt_or_ge (E % 3) 1 with h0 | h1
      · obtain ⟨q, rfl⟩ : ∃ q, E = 3 * (q + 1) := ⟨E / 3 - 1, by omega⟩
        exact ⟨⟨A + 9 * q + 9, 0, 0, 0, 5 * q + 7⟩,
          ⟨A + 9 * q + 9, 5 * q + 7, rfl, by omega, by omega⟩,
          by rw [show A = (A - q - 2) + q + 2 from by omega,
                 show (A - q - 2) + q + 2 + 9 * q + 9 = (A - q - 2) + 10 * q + 11 from by ring]
             exact trans_mod0 q (A - q - 2)⟩
      · rcases Nat.lt_or_ge (E % 3) 2 with h1' | h2
        · obtain ⟨q, rfl⟩ : ∃ q, E = 3 * q + 1 := ⟨E / 3, by omega⟩
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          exact ⟨⟨A + 9 * q' + 12, 0, 0, 0, 5 * q' + 8⟩,
            ⟨A + 9 * q' + 12, 5 * q' + 8, rfl, by omega, by omega⟩,
            by rw [show A = (A - q' - 3) + q' + 3 from by omega,
                   show (A - q' - 3) + q' + 3 + 9 * q' + 12 = (A - q' - 3) + 10 * q' + 15 from by ring]
               exact trans_mod1 q' (A - q' - 3)⟩
        · obtain ⟨q, rfl⟩ : ∃ q, E = 3 * q + 2 := ⟨E / 3, by omega⟩
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          exact ⟨⟨A + 9 * q' + 15, 0, 0, 0, 5 * q' + 9⟩,
            ⟨A + 9 * q' + 15, 5 * q' + 9, rfl, by omega, by omega⟩,
            by rw [show A = (A - q' - 3) + q' + 3 from by omega,
                   show (A - q' - 3) + q' + 3 + 9 * q' + 15 = (A - q' - 3) + 10 * q' + 18 from by ring]
               exact trans_mod2 q' (A - q' - 3)⟩
  · exact ⟨7, 4, rfl, by omega, by omega⟩
