import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #459: [28/15, 18/7, 1/6, 125/2, 7/5]

Vector representation:
```
 2 -1 -1  1
 1  2  0 -1
-1 -1  0  0
-1  0  3  0
 0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_459

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

-- R4 chain: (a+k, 0, c, 0) ->* (a, 0, c+3*k, 0)
theorem a_to_c : ∀ k, ∀ a c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+3*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R2,R1,R1 chain
theorem r2r1r1_chain : ∀ j, ∀ k c, ⟨5*k, 0, c+2*j, k+1⟩ [fm]⊢* ⟨5*(k+j), 0, c, k+j+1⟩ := by
  intro j; induction' j with j h <;> intro k c
  · simp; exists 0
  rw [show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring]
  step fm
  rw [show (c + 2 * j) + 2 = ((c + 2 * j) + 1) + 1 from by ring]
  step fm
  rw [show (c + 2 * j) + 1 = (c + 2 * j) + 1 from by ring]
  step fm
  apply stepStar_trans (h (k+1) c)
  ring_nf; finish

-- R2 chain (c=0): (a, b, 0, k) ->* (a+k, b+2*k, 0, 0)
theorem r2_chain : ∀ k, ∀ a b, ⟨a, b, 0, k⟩ [fm]⊢* ⟨a+k, b+2*k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3 chain: (a+k, k, 0, 0) ->* (a, 0, 0, 0)
theorem r3_chain : ∀ k, ∀ a, ⟨a+k, k, 0, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show (k + 1) = k + 1 from rfl]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- Opening: (0, 0, c+3, 0) -> (5, 0, c, 2) in 4 steps via R5,R2,R1,R1
theorem opening : ∀ c, ⟨0, 0, c+3, 0⟩ [fm]⊢* ⟨5, 0, c, 2⟩ := by
  intro c
  rw [show c + 3 = (c + 2) + 1 from by ring]
  step fm  -- R5: (0, 0, c+2, 1)
  step fm  -- R2: (1, 2, c+2, 0)
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm  -- R1: (3, 1, c+1, 1)
  step fm  -- R1: (5, 0, c, 2)
  finish

-- Main transition: (2*m+1, 0, 0, 0) ⊢⁺ (12*m+3, 0, 0, 0)
theorem main_trans (m : ℕ) : ⟨2*m+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨12*m+3, 0, 0, 0⟩ := by
  -- Phase 1: one R4 step
  apply step_stepStar_stepPlus
  · show fm ⟨2*m+1, 0, 0, 0⟩ = some ⟨2*m, 0, 3, 0⟩; simp [fm]
  -- Phase 1 cont: R4 chain (2*m, 0, 3, 0) ->* (0, 0, 3+3*(2*m), 0)
  apply stepStar_trans
  · have h := a_to_c (2*m) 0 3
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: opening (0, 0, 3+3*(2*m), 0) -> (5, 0, 3*(2*m), 2)
  apply stepStar_trans
  · rw [show 3 + 3 * (2 * m) = 3 * (2 * m) + 3 from by ring]
    exact opening (3*(2*m))
  -- Phase 3: R2,R1,R1 chain with 3*m rounds
  -- (5, 0, 3*(2*m), 2) = (5*1, 0, 0+2*(3*m), 1+1)
  apply stepStar_trans
  · rw [show 3 * (2 * m) = 0 + 2 * (3 * m) from by ring]
    exact r2r1r1_chain (3*m) 1 0
  -- (5*(1+3*m), 0, 0, 1+3*m+1)
  -- Phase 4: R2 chain
  apply stepStar_trans (r2_chain (1+3*m+1) (5*(1+3*m)) 0)
  -- Phase 5: R3 chain
  simp only [Nat.zero_add]
  rw [show 5 * (1 + 3 * m) + (1 + 3 * m + 1) = 12 * m + 3 + 2 * (1 + 3 * m + 1) from by ring]
  exact r3_chain (2*(1+3*m+1)) (12*m+3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun m ↦ ⟨2*m+1, 0, 0, 0⟩) 0
  intro m; exists 6*m+1
  rw [show 2 * (6 * m + 1) + 1 = 12 * m + 3 from by ring]
  exact main_trans m

end Sz22_2003_unofficial_459
