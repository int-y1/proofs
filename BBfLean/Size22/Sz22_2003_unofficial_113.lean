import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #113: [1/30, 7/2, 12/77, 25/7, 242/5]

Vector representation:
```
-1 -1 -1  0  0
-1  0  0  1  0
 2  1  0 -1 -1
 0  0  2 -1  0
 1  0 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_113

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- Phase 1: Big loop - one iteration: R5, R1
-- (0, b+1, c+2, 0, e) -> (1, b+1, c+1, 0, e+2) -> (0, b, c, 0, e+2)
theorem big_loop_one : ∀ b c e,
    ⟨0, b+1, c+2, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e+2⟩ := by
  intro b c e
  step fm; step fm; ring_nf; finish

-- Phase 1: Big loop - b iterations
theorem big_loop_iter : ∀ j, ∀ b c e,
    ⟨0, b+j, c+2*j, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e+2*j⟩ := by
  intro j; induction' j with j ih <;> intro b c e
  · exists 0
  rw [show b + (j + 1) = (b + j) + 1 from by ring,
      show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring]
  apply stepStar_trans (big_loop_one _ _ _)
  apply stepStar_trans (ih _ _ _)
  rw [show (e + 2) + 2 * j = e + 2 * (j + 1) from by ring]
  finish

-- Phase 2: Tail step: R5, R2, R3, R1
-- (0, 0, 2, 0, e) -> (1, 0, 1, 0, e+2) -> (0, 0, 1, 1, e+2)
-- -> (2, 1, 1, 0, e+1) -> (1, 0, 0, 0, e+1)
theorem tail_step : ∀ e,
    ⟨0, 0, 2, 0, e⟩ [fm]⊢* ⟨1, 0, 0, 0, e+1⟩ := by
  intro e
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Phase 3: R2
-- (1, 0, 0, 0, e) -> (0, 0, 0, 1, e)
-- (combined with phase 4 start)

-- Phase 4: R3, R2, R2 chain - one iteration
-- (0, b, 0, d+1, e+1) -> (2, b+1, 0, d, e) -> (1, b+1, 0, d+1, e) -> (0, b+1, 0, d+2, e)
theorem r3r2r2_one : ∀ b d e,
    ⟨0, b, 0, d+1, e+1⟩ [fm]⊢* ⟨0, b+1, 0, d+2, e⟩ := by
  intro b d e
  step fm; step fm; step fm; ring_nf; finish

-- Phase 4: R3, R2, R2 chain - j iterations
theorem r3r2r2_chain : ∀ j, ∀ b d e,
    ⟨0, b, 0, d+1, e+j⟩ [fm]⊢* ⟨0, b+j, 0, d+1+j, e⟩ := by
  intro j; induction' j with j ih <;> intro b d e
  · exists 0
  rw [show e + (j + 1) = (e + j) + 1 from by ring]
  apply stepStar_trans (r3r2r2_one _ _ _)
  rw [show d + 2 = (d + 1) + 1 from by ring]
  apply stepStar_trans (ih _ _ _)
  rw [show (d + 1 + 1) + j = d + 1 + (j + 1) from by ring,
      show (b + 1) + j = b + (j + 1) from by ring]
  finish

-- Phase 5: R4 chain - one iteration
-- (0, b, c, d+1, 0) -> (0, b, c+2, d, 0)
theorem r4_one : ∀ b c d,
    ⟨0, b, c, d+1, 0⟩ [fm]⊢* ⟨0, b, c+2, d, 0⟩ := by
  intro b c d
  step fm; finish

-- Phase 5: R4 chain - j iterations
theorem r4_chain : ∀ j, ∀ b c d,
    ⟨0, b, c, d+j, 0⟩ [fm]⊢* ⟨0, b, c+2*j, d, 0⟩ := by
  intro j; induction' j with j ih <;> intro b c d
  · exists 0
  rw [show d + (j + 1) = (d + j) + 1 from by ring]
  apply stepStar_trans (r4_one _ _ _)
  apply stepStar_trans (ih _ _ _)
  rw [show (c + 2) + 2 * j = c + 2 * (j + 1) from by ring]
  finish

-- Main transition: one full cycle
-- (0, b, 2*b+2, 0, 0) ->+ (0, 2*b+1, 2*(2*b+1)+2, 0, 0)
theorem main_trans (b : ℕ) :
    ⟨0, b, 2*b+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 2*b+1, 2*(2*b+1)+2, 0, 0⟩ := by
  -- Phase 1: big_loop b iterations
  -- (0, b, 2*b+2, 0, 0) ->* (0, 0, 2, 0, 2*b)
  apply stepStar_stepPlus_stepPlus
  · have h := big_loop_iter b 0 2 0
    simp only [(by ring : 0 + b = b),
               (by ring : 2 + 2 * b = 2 * b + 2),
               (by ring : 0 + 2 * b = 2 * b)] at h
    exact h
  -- Phase 2: tail step
  -- (0, 0, 2, 0, 2*b) ->* (1, 0, 0, 0, 2*b+1)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2, 0, 2 * b⟩ = some ⟨1, 0, 1, 0, 2 * b + 2⟩; rfl
  apply stepStar_trans
  · show ⟨1, 0, 1, 0, 2 * b + 2⟩ [fm]⊢* ⟨0, 0, 1, 1, 2 * b + 2⟩
    step fm; finish
  apply stepStar_trans
  · show ⟨0, 0, 1, 1, 2 * b + 2⟩ [fm]⊢* ⟨2, 1, 1, 0, 2 * b + 1⟩
    step fm; finish
  apply stepStar_trans
  · show ⟨2, 1, 1, 0, 2 * b + 1⟩ [fm]⊢* ⟨1, 0, 0, 0, 2 * b + 1⟩
    step fm; finish
  -- Phase 3: R2
  -- (1, 0, 0, 0, 2*b+1) -> (0, 0, 0, 1, 2*b+1)
  apply stepStar_trans
  · show ⟨1, 0, 0, 0, 2 * b + 1⟩ [fm]⊢* ⟨0, 0, 0, 1, 2 * b + 1⟩
    step fm; finish
  -- Phase 4: R3,R2,R2 chain (2*b+1 iterations)
  -- (0, 0, 0, 1, 2*b+1) ->* (0, 2*b+1, 0, 2*b+2, 0)
  apply stepStar_trans
  · have h := r3r2r2_chain (2*b+1) 0 0 0
    simp only [(by ring : 0 + (2 * b + 1) = 2 * b + 1),
               (by ring : 0 + 1 = 1),
               (by ring : 0 + 1 + (2 * b + 1) = 2 * b + 2)] at h
    exact h
  -- Phase 5: R4 chain (2*b+2 iterations)
  -- (0, 2*b+1, 0, 2*b+2, 0) ->* (0, 2*b+1, 4*b+4, 0, 0)
  have h := r4_chain (2*b+2) (2*b+1) 0 0
  simp only [(by ring : 0 + (2 * b + 2) = 2 * b + 2),
             (by ring : 0 + 2 * (2 * b + 2) = 4 * b + 4)] at h
  rw [show 2 * (2 * b + 1) + 2 = 4 * b + 4 from by ring]
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 4, 0, 0⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun b ↦ ⟨0, b, 2*b+2, 0, 0⟩) 1
  intro b
  exact ⟨2*b+1, main_trans b⟩

end Sz22_2003_unofficial_113
