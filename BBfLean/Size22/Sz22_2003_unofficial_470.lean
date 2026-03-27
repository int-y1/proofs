import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #470: [28/15, 21/22, 25/2, 11/7, 33/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  1 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_470

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- Phase 1: R4 drain d to e
theorem r4_drain : ∀ k, ∀ c d e,
    ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 2: R5 step
-- (0, 0, c+1, 0, e) -> (0, 1, c, 0, e+1)
-- This is just one step, handled inline.

-- Phase 3: Interleaved R1/R2 chain
-- Each round: (a, 1, k+1, d, k+1) -> R1 -> (a+2, 0, k, d+1, k+1) -> R2 -> (a+1, 1, k, d+2, k)
theorem r1r2_chain : ∀ k, ∀ a d,
    ⟨a, 1, k, d, k⟩ [fm]⊢* ⟨a + k, 1, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · simp; exists 0
  rw [show a + (k + 1) = (a + 1) + k from by ring,
      show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 4: R3 drain a, growing c by 2 each step
theorem r3_drain : ∀ k, ∀ c d,
    ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · simp; exists 0
  rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  finish

-- Cleanup: (c+2, 1, 0, 2c+4, 0) ->* (c+2, 0, 3, 2c+5, 0)
theorem cleanup (c : ℕ) :
    ⟨c + 2, 1, 0, 2 * (c + 2), 0⟩ [fm]⊢* ⟨c + 2, 0, 3, 2 * c + 5, 0⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Main transition: (0, 0, c+3, c+1, 0) ⊢⁺ (0, 0, 2*c+7, 2*c+5, 0)
theorem main_trans (c : ℕ) :
    ⟨0, 0, c + 3, c + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 7, 2 * c + 5, 0⟩ := by
  -- Phase 1: R4 drain: (0,0,c+3,c+1,0) ->* (0,0,c+3,0,c+1)
  apply stepStar_stepPlus_stepPlus
  · have h := r4_drain (c + 1) (c + 3) 0 0
    simp at h; exact h
  -- Phase 2: R5 step: (0,0,c+3,0,c+1) -> (0,1,c+2,0,c+2)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, c + 3, 0, c + 1⟩ = some ⟨0, 1, c + 2, 0, c + 2⟩; rfl
  -- Phase 3: R1/R2 chain (c+2 rounds): (0,1,c+2,0,c+2) ->* (c+2,1,0,2c+4,0)
  apply stepStar_trans
  · have h := r1r2_chain (c + 2) 0 0
    simp at h; exact h
  -- Phases 4-6: cleanup (c+2,1,0,2c+4,0) ->* (c+2,0,3,2c+5,0)
  apply stepStar_trans (cleanup c)
  -- Phase 7: R3 drain: (c+2,0,3,2c+5,0) ->* (0,0,2c+7,2c+5,0)
  have h := r3_drain (c + 2) 3 (2 * c + 5)
  rw [show 3 + 2 * (c + 2) = 2 * c + 7 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 3, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun c ↦ ⟨0, 0, c + 3, c + 1, 0⟩) 2
  intro c
  exact ⟨2 * c + 4, main_trans c⟩

end Sz22_2003_unofficial_470
