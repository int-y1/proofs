import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1748: [8/45, 147/2, 1/1029, 50/7]

Vector representation:
```
 3 -2 -1  0
-1  1  0  2
 0 -1  0 -3
 1  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1748

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d⟩ => some ⟨a+3, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+1, c, d+2⟩
  | ⟨a, b+1, c, d+3⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b, c+2, d⟩
  | _ => none

-- R4R2R3 chain: (0, 0, c, d+1+2*k) ->* (0, 0, c+2*k, d+1)
theorem r4r2r3_chain : ∀ k c d, ⟨0, 0, c, d + 1 + 2 * k⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + 1 + 2 * (k + 1) = (d + 2 + 2 * k) + 1 from by ring]
    step fm
    step fm
    rw [show (d + 2 + 2 * k) + 2 = (d + 1 + 2 * k) + 3 from by ring]
    step fm
    show ⟨0, 0, c + 2, d + 1 + 2 * k⟩ [fm]⊢* ⟨0, 0, c + 2 * (k + 1), d + 1⟩
    rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    exact ih (c + 2) d

-- Phase 1 tail: (0, 0, c, 1) -> (3, 0, c+3, 3) in 5 steps
-- (0,0,c,1) R4-> (1,0,c+2,0) R2-> (0,1,c+2,2) R4-> (1,1,c+4,1) R2-> (0,2,c+4,3) R1-> (3,0,c+3,3)
theorem phase1_tail : ⟨0, 0, c, 1⟩ [fm]⊢⁺ ⟨3, 0, c + 3, 3⟩ := by
  step fm  -- R4: (1, 0, c+2, 0)
  step fm  -- R2: (0, 1, c+2, 2)
  -- (0, 1, c+2, 2): step fm can't reduce because c+2 is symbolic.
  -- Use step_stepStar manually for this step.
  apply stepStar_trans
    (step_stepStar (show ⟨0, 1, c + 2, 2⟩ [fm]⊢ ⟨1, 1, c + 2 + 2, 1⟩ from by simp [fm]))
  rw [show c + 2 + 2 = c + 4 from by ring]
  step fm  -- R2: (0, 2, c+4, 3)
  step fm  -- R1: (3, 0, c+3, 3)
  finish

-- Phase 1 combined: (0, 0, 0, 2*n+3) ->+ (3, 0, 2*n+5, 3)
theorem phase1 : ⟨0, 0, 0, 2 * n + 3⟩ [fm]⊢⁺ ⟨3, 0, 2 * n + 5, 3⟩ := by
  rw [show 2 * n + 3 = 0 + 1 + 2 * (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4r2r3_chain (n + 1) 0 0)
  show ⟨0, 0, 0 + 2 * (n + 1), 0 + 1⟩ [fm]⊢⁺ ⟨3, 0, 2 * n + 5, 3⟩
  rw [show 0 + 2 * (n + 1) = 2 * n + 2 from by ring,
      show (0 : ℕ) + 1 = 1 from by ring,
      show 2 * n + 5 = (2 * n + 2) + 3 from by ring]
  exact phase1_tail

-- R2R2R1 chain: (a+3, 0, c+k, d) ->* (a+3+k, 0, c, d+4*k)
theorem r2r2r1_chain : ∀ k a c d, ⟨a + 3, 0, c + k, d⟩ [fm]⊢* ⟨a + 3 + k, 0, c, d + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    show ⟨a + 1 + 3, 0, c + k, d + 4⟩ [fm]⊢* ⟨a + 3 + (k + 1), 0, c, d + 4 * (k + 1)⟩
    rw [show a + 3 + (k + 1) = (a + 1) + 3 + k from by ring,
        show d + 4 * (k + 1) = (d + 4) + 4 * k from by ring]
    exact ih (a + 1) c (d + 4)

-- R2 drain: (k, b, 0, d) ->* (0, b+k, 0, d+2*k)
theorem r2_drain : ∀ k b d, ⟨k, b, 0, d⟩ [fm]⊢* ⟨0, b + k, 0, d + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    show ⟨k, b + 1, 0, d + 2⟩ [fm]⊢* ⟨0, b + (k + 1), 0, d + 2 * (k + 1)⟩
    rw [show b + (k + 1) = (b + 1) + k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    exact ih (b + 1) (d + 2)

-- R3 drain: (0, k, 0, d+3*k) ->* (0, 0, 0, d)
theorem r3_drain : ∀ k d, ⟨0, k, 0, d + 3 * k⟩ [fm]⊢* ⟨0, 0, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show d + 3 * (k + 1) = (d + 3 * k) + 3 from by ring]
    step fm
    exact ih d

-- Main transition: (0, 0, 0, 2*n+3) ->+ (0, 0, 0, 6*n+15)
theorem main_trans : ⟨0, 0, 0, 2 * n + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * n + 15⟩ := by
  apply stepPlus_stepStar_stepPlus phase1
  have h1 := r2r2r1_chain (2 * n + 5) 0 0 3
  rw [show (0 : ℕ) + 3 + (2 * n + 5) = 2 * n + 8 from by ring,
      show (0 : ℕ) + 3 = 3 from by ring,
      show (0 : ℕ) + (2 * n + 5) = 2 * n + 5 from by ring,
      show 3 + 4 * (2 * n + 5) = 8 * n + 23 from by ring] at h1
  apply stepStar_trans h1
  have h2 := r2_drain (2 * n + 8) 0 (8 * n + 23)
  rw [show (0 : ℕ) + (2 * n + 8) = 2 * n + 8 from by ring,
      show 8 * n + 23 + 2 * (2 * n + 8) = 12 * n + 39 from by ring] at h2
  apply stepStar_trans h2
  rw [show 12 * n + 39 = (6 * n + 15) + 3 * (2 * n + 8) from by ring]
  exact r3_drain (2 * n + 8) (6 * n + 15)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3⟩) (by execute fm 15)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n + 3⟩) 0
  intro n; exists 3 * n + 6
  show ⟨0, 0, 0, 2 * n + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * (3 * n + 6) + 3⟩
  rw [show 2 * (3 * n + 6) + 3 = 6 * n + 15 from by ring]
  exact main_trans
