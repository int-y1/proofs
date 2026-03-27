import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #303: [15/2, 40/63, 1/75, 1029/5]

Vector representation:
```
-1  1  1  0
 3 -2  1 -1
 0 -1 -2  0
 0  1 -1  3
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_303

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+1, c+1, d⟩
  | ⟨a, b+2, c, d+1⟩ => some ⟨a+3, b, c+1, d⟩
  | ⟨a, b+1, c+2, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d+3⟩
  | _ => none

-- One R4+R3 pair: (0, 0, c+3, d) ->* (0, 0, c, d+3)
theorem r4r3_pair : ∀ c d, ⟨0, 0, c+3, d⟩ [fm]⊢* ⟨0, 0, c, d+3⟩ := by
  intro c d
  step fm  -- R4: (0, 1, c+2, d+3)
  step fm  -- R3: (0, 0, c, d+3)
  finish

-- k iterations of R4+R3: (0, 0, 3*k+2, d) ->* (0, 0, 2, d+3*k)
theorem zigzag_chain : ∀ k d, ⟨0, 0, 3*k+2, d⟩ [fm]⊢* ⟨0, 0, 2, d+3*k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · simp; exists 0
  apply stepStar_trans (c₂ := ⟨0, 0, 3*k+2, d+3⟩)
  · have h := r4r3_pair (3*k+2) d
    rw [show 3 * k + 2 + 3 = 3 * (k + 1) + 2 from by ring] at h
    exact h
  have h := ih (d+3)
  rw [show d + 3 + 3 * k = d + 3 * (k + 1) from by ring] at h
  exact h

-- One climb step: R1 x 3 then R2
-- (3, j, 4*j+1, d+1) ->* (3, j+1, 4*j+5, d)
theorem climb_step : ∀ j d, ⟨3, j, 4*j+1, d+1⟩ [fm]⊢* ⟨3, j+1, 4*j+5, d⟩ := by
  intro j d
  step fm  -- R1: (2, j+1, 4*j+2, d+1)
  step fm  -- R1: (1, j+2, 4*j+3, d+1)
  step fm  -- R1: (0, j+3, 4*j+4, d+1)
  step fm  -- R2: (3, j+1, 4*j+5, d)
  finish

-- k climb steps: (3, j, 4*j+1, d+k) ->* (3, j+k, 4*(j+k)+1, d)
theorem climb_chain : ∀ k j d, ⟨3, j, 4*j+1, d+k⟩ [fm]⊢* ⟨3, j+k, 4*(j+k)+1, d⟩ := by
  intro k; induction' k with k ih <;> intro j d
  · simp; exists 0
  rw [show d + (k + 1) = d + k + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨3, j+1, 4*j+5, d+k⟩)
  · exact climb_step j (d+k)
  have h := ih (j+1) d
  rw [show 4 * (j + 1) + 1 = 4 * j + 5 from by ring,
      show j + 1 + k = j + (k + 1) from by ring] at h
  exact h

-- R3 descent one step: (0, b+1, c+2, 0) -> (0, b, c, 0)
theorem r3_one (b c : ℕ) : ⟨0, b+1, c+2, 0⟩ [fm]⊢ ⟨0, b, c, 0⟩ := by
  show fm ⟨0, b+1, c+2, 0⟩ = some ⟨0, b, c, 0⟩
  simp [fm]

-- R3 descent: (0, b+k, c+2*k, 0) ->* (0, b, c, 0)
theorem r3_descent : ∀ k b c, ⟨0, b+k, c+2*k, 0⟩ [fm]⊢* ⟨0, b, c, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · simp; exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  exact stepStar_trans (step_stepStar (r3_one (b+k) (c+2*k))) (ih b c)

-- Main transition: (0, 0, 3*n+2, 0) ->+ (0, 0, 6*n+8, 0)
-- 6*n+8 = 3*(2*n+2)+2, so this maps C(n) to C(2*n+2)
theorem main_trans (n : ℕ) : ⟨0, 0, 3*n+2, 0⟩ [fm]⊢⁺ ⟨0, 0, 6*n+8, 0⟩ := by
  -- Phase 1: zigzag to (0, 0, 2, 3*n)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2, 3*n⟩)
  · have h := zigzag_chain n 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4, R4, R2
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2, 3*n⟩ = some ⟨0, 1, 1, 3*n+3⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 2, 0, 3*n+6⟩)
  · apply step_stepStar
    show fm ⟨0, 1, 1, 3*n+3⟩ = some ⟨0, 2, 0, 3*n+6⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨3, 0, 1, 3*n+5⟩)
  · apply step_stepStar
    show fm ⟨0, 0+2, 0, (3*n+5)+1⟩ = some ⟨0+3, 0, 0+1, 3*n+5⟩
    simp [fm]
  -- Phase 3: climb (3*n+5) steps
  apply stepStar_trans (c₂ := ⟨3, 3*n+5, 4*(3*n+5)+1, 0⟩)
  · have h := climb_chain (3*n+5) 0 0
    simp only [Nat.zero_add] at h
    rw [show 4 * 0 + 1 = 1 from rfl] at h; exact h
  -- Phase 4: finish climb R1 x 3
  rw [show 4 * (3 * n + 5) + 1 = 12 * n + 21 from by ring]
  apply stepStar_trans (c₂ := ⟨0, 3*n+8, 12*n+24, 0⟩)
  · apply stepStar_trans (step_stepStar (by
      show fm ⟨3, 3*n+5, 12*n+21, 0⟩ = some ⟨2, 3*n+6, 12*n+22, 0⟩
      simp [fm]))
    apply stepStar_trans (step_stepStar (by
      show fm ⟨2, 3*n+6, 12*n+22, 0⟩ = some ⟨1, 3*n+7, 12*n+23, 0⟩
      simp [fm]))
    apply step_stepStar
    show fm ⟨1, 3*n+7, 12*n+23, 0⟩ = some ⟨0, 3*n+8, 12*n+24, 0⟩
    simp [fm]
  -- Phase 5: R3 descent
  have h := r3_descent (3*n+8) 0 (6*n+8)
  rw [show 0 + (3 * n + 8) = 3 * n + 8 from by ring,
      show 6 * n + 8 + 2 * (3 * n + 8) = 12 * n + 24 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0⟩) (by execute fm 19)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, 3*n+2, 0⟩) 0
  intro n
  exact ⟨2*n+2, by rw [show 3 * (2 * n + 2) + 2 = 6 * n + 8 from by ring]; exact main_trans n⟩

end Sz22_2003_unofficial_303
