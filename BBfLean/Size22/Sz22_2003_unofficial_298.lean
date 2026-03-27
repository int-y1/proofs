import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #298: [15/2, 1/1617, 22/39, 1183/5, 3/11]

Vector representation:
```
-1  1  1  0  0  0
 0 -1  0 -2 -1  0
 1 -1  0  0  1 -1
 0  0 -1  1  0  2
 0  1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6

The machine repeatedly visits (0, 1, 0, 1, 0, f) with f doubling each time:
2, 4, 8, 16, 32, ...
-/

namespace Sz22_2003_unofficial_298

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | ⟨a, b+1, c, d+2, e+1, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+2⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- Phase 1: R3+R1 loop. Each iteration: (0,1,c,1,e,f+1) -> (1,0,c,1,e+1,f) -> (0,1,c+1,1,e+1,f)
-- After k iterations: (0,1,c,1,e,f+k) ->* (0,1,c+k,1,e+k,f)
theorem phase1 : ⟨0, 1, c, 1, e, f + k⟩ [fm]⊢* ⟨0, 1, c + k, 1, e + k, f⟩ := by
  have h : ∀ k c e, ⟨0, 1, c, 1, e, f + k⟩ [fm]⊢* ⟨0, 1, c + k, 1, e + k, f⟩ := by
    intro k; induction' k with k ih <;> intro c e
    · exists 0
    rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact h k c e

-- Phase 2: (0, 1, n+1, 1, n+1, 0) -> R4 -> (0, 1, n, 2, n+1, 2) -> R2 -> (0, 0, n, 0, n, 2)
theorem phase2 : ⟨0, 1, n+1, 1, n+1, 0⟩ [fm]⊢⁺ ⟨0, 0, n, 0, n, 2⟩ := by
  step fm; step fm; finish

-- Phase 3: R4 loop. Each iteration: (0,0,c+1,d,e,f) -> (0,0,c,d+1,e,f+2)
-- After k iterations: (0, 0, c+k, d, e, f) ->* (0, 0, c, d+k, e, f+2*k)
theorem phase3 : ⟨0, 0, c + k, d, e, f⟩ [fm]⊢* ⟨0, 0, c, d + k, e, f + 2*k⟩ := by
  have h : ∀ k c d f, ⟨0, 0, c + k, d, e, f⟩ [fm]⊢* ⟨0, 0, c, d + k, e, f + 2*k⟩ := by
    intro k; induction' k with k ih <;> intro c d f
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish
  exact h k c d f

-- Phase 4: R5+R2 drain loop.
-- (0, 0, 0, 2*k+1, 2*k+1, f) -> ... -> (0, 1, 0, 1, 0, f)
theorem phase4 : ⟨0, 0, 0, 2*k+1, 2*k+1, f⟩ [fm]⊢* ⟨0, 1, 0, 1, 0, f⟩ := by
  have h : ∀ k, ⟨0, 0, 0, 2*k+1, 2*k+1, f⟩ [fm]⊢* ⟨0, 1, 0, 1, 0, f⟩ := by
    intro k; induction' k with k ih
    · step fm; finish
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm
    exact ih
  exact h k

-- Main cycle: (0, 1, 0, 1, 0, 2*(k+1)) ->+ (0, 1, 0, 1, 0, 4*(k+1))
theorem cycle : ⟨0, 1, 0, 1, 0, 2*(k+1)⟩ [fm]⊢⁺ ⟨0, 1, 0, 1, 0, 4*(k+1)⟩ := by
  -- Phase 1: (0, 1, 0, 1, 0, 2*(k+1)) ->* (0, 1, 2*(k+1), 1, 2*(k+1), 0)
  rw [show 2*(k+1) = 0 + (2*(k+1)) from by ring]
  apply stepStar_stepPlus_stepPlus (phase1 (f := 0) (k := 2*(k+1)))
  simp only [Nat.zero_add]
  -- Phase 2: (0, 1, 2*(k+1), 1, 2*(k+1), 0) ->+ (0, 0, 2*k+1, 0, 2*k+1, 2)
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus phase2
  -- Phase 3: (0, 0, 2*k+1, 0, 2*k+1, 2) ->* (0, 0, 0, 2*k+1, 2*k+1, 2+2*(2*k+1))
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_trans (phase3 (c := 0) (d := 0) (k := 2*k+1) (f := 2))
  simp only [Nat.zero_add]
  -- Phase 4: drain to (0, 1, 0, 1, 0, 4*(k+1))
  rw [show 2 + 2 * (2 * k + 1) = 4 * (k + 1) from by ring]
  exact phase4

theorem nonhalt : ¬halts fm c₀ := by
  -- c₀ = (1, 0, 0, 0, 0, 0) ->* (0, 1, 0, 1, 0, 2)
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 1, 0, 2⟩)
  · execute fm 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k, q = ⟨0, 1, 0, 1, 0, 2*(k+1)⟩)
  · intro c ⟨k, hq⟩; subst hq
    exact ⟨⟨0, 1, 0, 1, 0, 4*(k+1)⟩, ⟨2*k+1, by ring_nf⟩, cycle⟩
  · exact ⟨0, by ring_nf⟩
