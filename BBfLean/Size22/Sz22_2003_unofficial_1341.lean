import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1341: [63/10, 2/33, 9317/2, 5/7, 3/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  1  3
 0  0  1 -1  0
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1341

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k d e, ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), k, d, e⟩ := by
  intro k; induction' k with k ih
  · intro d e; exists 0
  · intro d e
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (d + 1) e)
    step fm; finish

theorem r1r2_chain : ∀ c k, ⟨(1 : ℕ), k, c + 1, k, c + 1⟩ [fm]⊢* ⟨(1 : ℕ), k + c + 1, 0, k + c + 1, 0⟩ := by
  intro c; induction' c with c ih
  · intro k; step fm; step fm; finish
  · intro k
    step fm; step fm
    apply stepStar_trans (ih (k + 1))
    ring_nf; finish

theorem r3_chain : ∀ a D e, ⟨a, (0 : ℕ), (0 : ℕ), D, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + a, e + 3 * a⟩ := by
  intro a; induction' a with a ih
  · intro D e; exists 0
  · intro D e; step fm
    apply stepStar_trans (ih (D + 1) (e + 3))
    ring_nf; finish

theorem r3r2x3_one (a b D : ℕ) :
    ⟨a + 1, b + 3, (0 : ℕ), D, (0 : ℕ)⟩ [fm]⊢* ⟨a + 3, b, (0 : ℕ), D + 1, (0 : ℕ)⟩ := by
  step fm
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨a, b + 3, 0, D + 1, 3⟩ : Q) [fm]⊢ ⟨a + 1, b + 2, 0, D + 1, 2⟩))
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨a + 1, b + 2, 0, D + 1, 2⟩ : Q) [fm]⊢ ⟨a + 2, b + 1, 0, D + 1, 1⟩))
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨a + 2, b + 1, 0, D + 1, 1⟩ : Q) [fm]⊢ ⟨a + 3, b, 0, D + 1, 0⟩))
  finish

theorem r3r2x3_cycle : ∀ j a b D, ⟨a + 1, b + 3 * j, (0 : ℕ), D, (0 : ℕ)⟩ [fm]⊢* ⟨a + 1 + 2 * j, b, (0 : ℕ), D + j, (0 : ℕ)⟩ := by
  intro j; induction' j with j ih
  · intro a b D; simp; exists 0
  · intro a b D
    rw [show b + 3 * (j + 1) = (b + 3) + 3 * j from by ring]
    apply stepStar_trans (ih a (b + 3) D)
    rw [show a + 1 + 2 * j = (a + 2 * j) + 1 from by ring]
    apply stepStar_trans (r3r2x3_one (a + 2 * j) b (D + j))
    rw [show a + 2 * j + 3 = a + 1 + 2 * (j + 1) from by ring,
        show D + j + 1 = D + (j + 1) from by ring]
    finish

theorem end_b1 (a D : ℕ) :
    ⟨a + 1, 1, (0 : ℕ), D, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + a + 2, 3 * a + 5⟩ := by
  step fm
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨a, 1, 0, D + 1, 3⟩ : Q) [fm]⊢ ⟨a + 1, 0, 0, D + 1, 2⟩))
  apply stepStar_trans (r3_chain (a + 1) (D + 1) 2)
  ring_nf; finish

theorem end_b2 (a D : ℕ) :
    ⟨a + 1, 2, (0 : ℕ), D, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), D + a + 3, 3 * a + 7⟩ := by
  step fm
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨a, 2, 0, D + 1, 3⟩ : Q) [fm]⊢ ⟨a + 1, 1, 0, D + 1, 2⟩))
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨a + 1, 1, 0, D + 1, 2⟩ : Q) [fm]⊢ ⟨a + 2, 0, 0, D + 1, 1⟩))
  apply stepStar_trans (r3_chain (a + 2) (D + 1) 1)
  ring_nf; finish

-- Full transition for d ≡ 2 mod 3 (d = 3m+2): compose all phases inline
theorem case_mod2 (m : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 3 * m + 3, 3 * m + 5⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 6 * m + 7, 6 * m + 9⟩ := by
  -- Phase 1: R4 chain
  rw [show 3 * m + 3 = 0 + (3 * m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (3 * m + 3) 0 (3 * m + 5))
  -- Phase 2: R5+R2
  rw [show 3 * m + 5 = (3 * m + 4) + 1 from by ring]
  step fm
  rw [show 3 * m + 4 = (3 * m + 3) + 1 from by ring]
  step fm
  -- Phase 3: R1R2 chain
  rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring]
  apply stepStar_trans (r1r2_chain (3 * m + 2) 0)
  rw [show 0 + (3 * m + 2) + 1 = 3 * m + 3 from by ring]
  -- Phase 4: R3
  step fm
  -- Phase 5: R2x3
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 3 * m + 3, 0, 3 * m + 4, 3⟩ : Q) [fm]⊢ ⟨1, 3 * m + 2, 0, 3 * m + 4, 2⟩))
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨1, 3 * m + 2, 0, 3 * m + 4, 2⟩ : Q) [fm]⊢ ⟨2, 3 * m + 1, 0, 3 * m + 4, 1⟩))
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨2, 3 * m + 1, 0, 3 * m + 4, 1⟩ : Q) [fm]⊢ ⟨3, 3 * m, 0, 3 * m + 4, 0⟩))
  -- Phase 6: r3r2x3 cycle with j=m, then R3 chain
  -- State: (3, 3*m, 0, 3*m+4, 0) = (2+1, 0+3*m, 0, 3*m+4, 0)
  -- r3r2x3_cycle expects (a+1, b+3*j, 0, D, 0)
  -- a=2, b=0, j=m, D=3*m+4
  -- But 3 = 2+1 (def eq), 3*m = 0+3*m (NOT def eq)
  rw [show (3 * m : ℕ) = 0 + 3 * m from by ring]
  apply stepStar_trans (r3r2x3_cycle m 2 0 (0 + 3 * m + 4))
  apply stepStar_trans (r3_chain (2 + 1 + 2 * m) (0 + 3 * m + 4 + m) 0)
  ring_nf; finish

theorem case_mod0 (m : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 3 * m + 4, 3 * m + 6⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 6 * m + 9, 6 * m + 11⟩ := by
  rw [show 3 * m + 4 = 0 + (3 * m + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (3 * m + 4) 0 (3 * m + 6))
  rw [show 3 * m + 6 = (3 * m + 5) + 1 from by ring]
  step fm
  rw [show 3 * m + 5 = (3 * m + 4) + 1 from by ring]
  step fm
  rw [show 3 * m + 4 = (3 * m + 3) + 1 from by ring]
  apply stepStar_trans (r1r2_chain (3 * m + 3) 0)
  rw [show 0 + (3 * m + 3) + 1 = 3 * m + 4 from by ring]
  step fm
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 3 * m + 4, 0, 3 * m + 5, 3⟩ : Q) [fm]⊢ ⟨1, 3 * m + 3, 0, 3 * m + 5, 2⟩))
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨1, 3 * m + 3, 0, 3 * m + 5, 2⟩ : Q) [fm]⊢ ⟨2, 3 * m + 2, 0, 3 * m + 5, 1⟩))
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨2, 3 * m + 2, 0, 3 * m + 5, 1⟩ : Q) [fm]⊢ ⟨3, 3 * m + 1, 0, 3 * m + 5, 0⟩))
  -- (3, 3m+1, 0, 3m+5, 0) = (2+1, 1+3*m, 0, 3m+5, 0)
  rw [show 3 * m + 1 = 1 + 3 * m from by ring]
  apply stepStar_trans (r3r2x3_cycle m 2 1 (3 * m + 5))
  rw [show 2 + 1 + 2 * m = (2 * m + 2) + 1 from by ring,
      show 3 * m + 5 + m = 4 * m + 5 from by ring]
  apply stepStar_trans (end_b1 (2 * m + 2) (4 * m + 5))
  ring_nf; finish

theorem case_mod1 (m : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 3 * m + 5, 3 * m + 7⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 6 * m + 11, 6 * m + 13⟩ := by
  rw [show 3 * m + 5 = 0 + (3 * m + 5) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (3 * m + 5) 0 (3 * m + 7))
  rw [show 3 * m + 7 = (3 * m + 6) + 1 from by ring]
  step fm
  rw [show 3 * m + 6 = (3 * m + 5) + 1 from by ring]
  step fm
  rw [show 3 * m + 5 = (3 * m + 4) + 1 from by ring]
  apply stepStar_trans (r1r2_chain (3 * m + 4) 0)
  rw [show 0 + (3 * m + 4) + 1 = 3 * m + 5 from by ring]
  step fm
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 3 * m + 5, 0, 3 * m + 6, 3⟩ : Q) [fm]⊢ ⟨1, 3 * m + 4, 0, 3 * m + 6, 2⟩))
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨1, 3 * m + 4, 0, 3 * m + 6, 2⟩ : Q) [fm]⊢ ⟨2, 3 * m + 3, 0, 3 * m + 6, 1⟩))
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨2, 3 * m + 3, 0, 3 * m + 6, 1⟩ : Q) [fm]⊢ ⟨3, 3 * m + 2, 0, 3 * m + 6, 0⟩))
  -- (3, 3m+2, 0, 3m+6, 0) = (2+1, 2+3*m, 0, 3m+6, 0)
  rw [show 3 * m + 2 = 2 + 3 * m from by ring]
  apply stepStar_trans (r3r2x3_cycle m 2 2 (3 * m + 6))
  rw [show 2 + 1 + 2 * m = (2 * m + 2) + 1 from by ring,
      show 3 * m + 6 + m = 4 * m + 6 from by ring]
  apply stepStar_trans (end_b2 (2 * m + 2) (4 * m + 6))
  ring_nf; finish

theorem main_transition (d : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 1, d + 3⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * d + 3, 2 * d + 5⟩ := by
  rcases d with _ | _ | d
  · show ⟨(0 : ℕ), 0, 0, 1, 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 3, 5⟩
    execute fm 8
  · show ⟨(0 : ℕ), 0, 0, 2, 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 5, 7⟩
    execute fm 13
  · obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, d = 3 * m ∨ d = 3 * m + 1 ∨ d = 3 * m + 2 := ⟨d / 3, by omega⟩
    · rw [show 3 * m + 2 + 1 = 3 * m + 3 from by ring,
          show 3 * m + 2 + 3 = 3 * m + 5 from by ring,
          show 2 * (3 * m + 2) + 3 = 6 * m + 7 from by ring,
          show 2 * (3 * m + 2) + 5 = 6 * m + 9 from by ring]
      exact case_mod2 m
    · rw [show 3 * m + 1 + 2 + 1 = 3 * m + 4 from by ring,
          show 3 * m + 1 + 2 + 3 = 3 * m + 6 from by ring,
          show 2 * (3 * m + 1 + 2) + 3 = 6 * m + 9 from by ring,
          show 2 * (3 * m + 1 + 2) + 5 = 6 * m + 11 from by ring]
      exact case_mod0 m
    · rw [show 3 * m + 2 + 2 + 1 = 3 * m + 5 from by ring,
          show 3 * m + 2 + 2 + 3 = 3 * m + 7 from by ring,
          show 2 * (3 * m + 2 + 2) + 3 = 6 * m + 11 from by ring,
          show 2 * (3 * m + 2 + 2) + 5 = 6 * m + 13 from by ring]
      exact case_mod1 m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d + 1, d + 3⟩) 0
  intro d; exists 2 * d + 2
  exact main_transition d

end Sz22_2003_unofficial_1341
