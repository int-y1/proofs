import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #559: [315/2, 1/55, 2/65, 143/3, 25/77]

Vector representation:
```
-1  2  1  1  0  0
 0  0 -1  0 -1  0
 1  0 -1  0  0 -1
 0 -1  0  0  1  1
 0  0  2 -1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_559

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+2, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a, b, c+2, d, e, f⟩
  | _ => none

-- R3/R1 alternating chain: (0, b, 2, d, 0, k) →* (0, b+2*k, 2, d+k, 0, 0)
theorem r3r1_chain : ∀ k, ∀ b d, ⟨0, b, 2, d, 0, k⟩ [fm]⊢* ⟨0, b+2*k, 2, d+k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R4 drain: (0, k, 0, d, e, f) →* (0, 0, 0, d, e+k, f+k)
theorem r4_drain : ∀ k, ∀ d e f, ⟨0, k, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d, e+k, f+k⟩ := by
  intro k; induction' k with k h <;> intro d e f
  · exists 0
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5/R2/R2 chain: (0, 0, 0, d+k, 3*k+1, f) →* (0, 0, 0, d, 1, f)
theorem r5r2r2_chain : ∀ k, ∀ d f, ⟨0, 0, 0, d+k, 3*k+1, f⟩ [fm]⊢* ⟨0, 0, 0, d, 1, f⟩ := by
  intro k; induction' k with k h <;> intro d f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show 3 * (k + 1) + 1 = (3 * k + 1) + 3 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Middle phase: 6 fixed steps from (0, B, 2, D, 0, 0) to (0, B, 0, D+1, 0, 1)
-- R4: (0, B-1, 2, D, 1, 1)
-- R2: (0, B-1, 1, D, 0, 1)
-- R3: (1, B-1, 0, D, 0, 0)
-- R1: (0, B+1, 1, D+1, 0, 0)
-- R4: (0, B, 1, D+1, 1, 1)
-- R2: (0, B, 0, D+1, 0, 1)
theorem middle_phase : ⟨0, b+1, 2, d, 0, 0⟩ [fm]⊢* ⟨0, b+1, 0, d+1, 0, 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- Main transition: canonical → canonical
-- (0, 0, 2, d, 0, 3*g+2) →⁺ (0, 0, 2, d+g+1, 0, 6*g+5)
theorem main_trans : ⟨0, 0, 2, d, 0, 3*g+2⟩ [fm]⊢⁺ ⟨0, 0, 2, d+g+1, 0, 6*g+5⟩ := by
  -- Phase 1: R3/R1 chain consuming f = 3*g+2
  apply stepStar_stepPlus_stepPlus (r3r1_chain (3*g+2) 0 d)
  -- State: (0, 6*g+4, 2, d+3*g+2, 0, 0)
  -- Phase 2: middle_phase (6 steps)
  rw [show 0 + 2 * (3 * g + 2) = (6 * g + 3) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (middle_phase)
  -- State: (0, 6*g+4, 0, d+3*g+3, 0, 1)
  rw [show d + (3 * g + 2) + 1 = d + 3 * g + 3 from by ring]
  -- Phase 3: R4 drain (6*g+4 steps)
  rw [show 6 * g + 3 + 1 = 6 * g + 4 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (6*g+4) (d+3*g+3) 0 1)
  -- State: (0, 0, 0, d+3*g+3, 6*g+4, 6*g+5)
  -- Phase 4: R5/R2/R2 chain (2*g+1 rounds)
  rw [show d + 3 * g + 3 = (d + g + 2) + (2 * g + 1) from by ring,
      show 0 + (6 * g + 4) = 3 * (2 * g + 1) + 1 from by ring,
      show 1 + (6 * g + 4) = 6 * g + 5 from by ring]
  apply stepStar_stepPlus_stepPlus (r5r2r2_chain (2*g+1) (d+g+2) (6*g+5))
  -- State: (0, 0, 0, d+g+2, 1, 6*g+5)
  -- Phase 5: Final R5 step
  rw [show d + g + 2 = (d + g + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0, 2⟩)
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, g⟩ ↦ ⟨0, 0, 2, d, 0, 3*g+2⟩) ⟨0, 0⟩
  intro ⟨d, g⟩; exact ⟨⟨d+g+1, 2*g+1⟩, by
    show ⟨0, 0, 2, d, 0, 3*g+2⟩ [fm]⊢⁺ ⟨0, 0, 2, d+g+1, 0, 3*(2*g+1)+2⟩
    rw [show 3 * (2 * g + 1) + 2 = 6 * g + 5 from by ring]
    exact main_trans⟩

end Sz22_2003_unofficial_559
