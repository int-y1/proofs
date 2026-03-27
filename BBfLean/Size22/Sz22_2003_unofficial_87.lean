import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #87: [1/30, 147/2, 2/77, 25/7, 242/5]

Vector representation:
```
-1 -1 -1  0  0
-1  1  0  2  0
 1  0  0 -1 -1
 0  0  2 -1  0
 1  0 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_87

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- Phase 1: R2/R3 chain
-- (1, b, 0, d, k) ->* (0, b+k+1, 0, d+k+2, 0)
-- Each iteration: R2 then R3 (while k > 0), final R2
theorem phase1 : ∀ k b d, ⟨1, b, 0, d, k⟩ [fm]⊢* ⟨0, b+k+1, 0, d+k+2, 0⟩ := by
  intro k; induction' k with k h <;> intro b d
  · step fm; ring_nf; finish
  rw [show k + 1 = k + 1 from rfl]
  step fm  -- R2: (0, b+1, 0, d+2, k+1)
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm  -- R3: (1, b+1, 0, d+1, k)
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Phase 2: R4 chain
-- (0, b, c, d+k, 0) ->* (0, b, c+2*k, d, 0)
theorem phase2 : ∀ k b c d, ⟨0, b, c, d+k, 0⟩ [fm]⊢* ⟨0, b, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro b c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm  -- R4: (0, b, c+2, d+k, 0)
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 3: R5/R1 chain
-- (0, k+1, c+2*(k+1), 0, e) ->* (0, 0, c, 0, e+2*(k+1))
-- Each round: R5, R1
theorem phase3 : ∀ k, ∀ c e, ⟨0, k+1, c+2*(k+1), 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e+2*(k+1)⟩ := by
  intro k; induction' k with k h <;> intro c e
  · rw [show c + 2 * 1 = c + 1 + 1 from by ring]
    step fm
    step fm
    ring_nf; finish
  · rw [show c + 2 * (k + 1 + 1) = (c + 2 * (k + 1)) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish

-- Main transition: (1, 0, 0, 0, e) ⊢⁺ (1, 0, 0, 0, 2*e+2)
theorem main_trans (e : ℕ) : ⟨1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2*e+2⟩ := by
  -- Phase 1: (1,0,0,0,e) ->* (0, e+1, 0, e+2, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := phase1 e 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 2: (0, e+1, 0, e+2, 0) ->* (0, e+1, 2*(e+2), 0, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := phase2 (e+2) (e+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: (0, e+1, 2*(e+2), 0, 0) ->* (0, 0, 2, 0, 2*(e+1))
  apply stepStar_stepPlus_stepPlus
  · have h := phase3 e 2 0
    simp only [Nat.zero_add, (by ring : 2 + 2 * (e + 1) = 2 * (e + 2))] at h
    exact h
  -- Phase 4: (0, 0, 2, 0, 2*(e+1)) -> (1, 0, 0, 0, 2*e+2) in 5 steps: R5, R2, R3, R1, R3
  step fm
  step fm
  rw [show 2 = 1 + 1 from rfl]
  rw [show 2 * (e + 1) + 2 = (2 * (e + 1) + 1) + 1 from by ring]
  step fm
  step fm
  rw [show 2 * (e + 1) + 1 = (2 * e + 2) + 1 from by ring]
  step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun e ↦ ⟨1, 0, 0, 0, e⟩) 0
  intro e; exists 2*e+2; exact main_trans e

end Sz22_2003_unofficial_87
