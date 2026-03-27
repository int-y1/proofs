import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #183: [1/6, 175/2, 2/55, 3/5, 11/21, 2/3]

Vector representation:
```
-1 -1  0  0  0
-1  0  2  1  0
 1  0 -1  0 -1
 0  1 -1  0  0
 0 -1  0 -1  1
 1 -1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_183

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R2/R3 spiral: j iterations of alternating R2, R3
-- From (1, 0, j, j, e) we apply R2 then R3 to get (1, 0, j+1, j+1, e-1)
-- Starting from (1, 0, 0, 0, e+j), after j pairs we get (1, 0, j, j, e)
theorem r2r3_spiral : ∀ j, ∀ e,
    ⟨1, 0, 0, 0, e + j⟩ [fm]⊢* ⟨1, 0, j, j, e⟩ := by
  intro j; induction' j with j ih <;> intro e
  · exists 0
  rw [show e + (j + 1) = e + j + 1 from by ring]
  apply stepStar_trans
  · rw [show e + j + 1 = (e + 1) + j from by ring]
    exact ih (e + 1)
  step fm; step fm
  ring_nf; finish

-- R4 chain: transfer c to b
-- (0, b, c+j, d, 0) ->* (0, b+j, c, d, 0)
theorem r4_chain : ∀ j, ∀ b c d,
    ⟨0, b, c + j, d, 0⟩ [fm]⊢* ⟨0, b + j, c, d, 0⟩ := by
  intro j; induction' j with j ih <;> intro b c d
  · exists 0
  rw [show c + (j + 1) = (c + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5 chain: transfer d to e (when c=0)
-- (0, b+j, 0, d+j, e) ->* (0, b, 0, d, e+j)
theorem r5_chain : ∀ j, ∀ b d e,
    ⟨0, b + j, 0, d + j, e⟩ [fm]⊢* ⟨0, b, 0, d, e + j⟩ := by
  intro j; induction' j with j ih <;> intro b d e
  · exists 0
  rw [show b + (j + 1) = (b + j) + 1 from by ring,
      show d + (j + 1) = (d + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  rw [show (e + 1) + j = e + (j + 1) from by ring]
  finish

-- Main transition: (1, 0, 0, 0, n+1) ->+ (1, 0, 0, 0, n+2)
-- Phase A: R2/R3 spiral n+1 times: (1,0,0,0,n+1) ->* (1,0,n+1,n+1,0)
-- Phase B: final R2: (1,0,n+1,n+1,0) -> (0,0,n+3,n+2,0)
-- Phase C: R4 chain n+3 times: (0,0,n+3,n+2,0) ->* (0,n+3,0,n+2,0)
-- Phase D: R5 chain n+2 times: (0,n+3,0,n+2,0) ->* (0,1,0,0,n+2)
-- Phase E: R6: (0,1,0,0,n+2) -> (1,0,0,0,n+2)
theorem main_trans (n : ℕ) :
    ⟨1, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, n + 2⟩ := by
  -- Phase A: R2/R3 spiral
  apply stepStar_stepPlus_stepPlus
  · have h := r2r3_spiral (n + 1) 0
    simp only [(by ring : 0 + (n + 1) = n + 1)] at h
    exact h
  -- Phase B: final R2
  apply step_stepStar_stepPlus
  · show fm ⟨1, 0, n + 1, n + 1, 0⟩ = some ⟨0, 0, n + 3, n + 2, 0⟩; rfl
  -- Phase C: R4 chain
  apply stepStar_trans
  · have h := r4_chain (n + 3) 0 0 (n + 2)
    simp only [(by ring : 0 + (n + 3) = n + 3)] at h
    exact h
  -- Phase D: R5 chain
  apply stepStar_trans
  · have h := r5_chain (n + 2) 1 0 0
    simp only [(by ring : 1 + (n + 2) = n + 3),
               (by ring : 0 + (n + 2) = n + 2)] at h
    exact h
  -- Phase E: R6
  step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, 0, n + 1⟩) 0
  intro n
  exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_183
