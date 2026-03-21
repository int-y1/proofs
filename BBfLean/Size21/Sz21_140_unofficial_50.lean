import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #50: [35/6, 4/55, 847/2, 3/7, 2/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_50

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- Phase 1: R3 repeated: each step (a+1, 0, 0, D, E) → (a, 0, 0, D+1, E+2)
theorem r3_chain : ∀ k, ∀ a D E, ⟨a+k, 0, 0, D, E⟩ [fm]⊢* ⟨a, 0, 0, D+k, E+2*k⟩ := by
  intro k; induction' k with k h <;> intro a D E
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2: R4 repeated: each step (0, b, 0, D+1, E) → (0, b+1, 0, D, E)
theorem r4_chain : ∀ k, ∀ b D E, ⟨0, b, 0, D+k, E⟩ [fm]⊢* ⟨0, b+k, 0, D, E⟩ := by
  intro k; induction' k with k h <;> intro b D E
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2 chain: each step (a, 0, C+1, D, E+1) → (a+2, 0, C, D, E)
theorem r2_chain : ∀ k, ∀ a C D, ⟨a, 0, C+k, D, k⟩ [fm]⊢* ⟨a+2*k, 0, C, D, 0⟩ := by
  intro k; induction' k with k h <;> intro a C D
  · exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- One R1x2R2 round: 3 steps
-- (2, B+2, C, D, E+1) → R1 → (1, B+1, C+1, D+1, E+1)
--                      → R1 → (0, B, C+2, D+2, E+1)
--                      → R2 → (2, B, C+1, D+2, E)
theorem r1r1r2_one : ∀ B C D E, ⟨2, B+2, C, D, E+1⟩ [fm]⊢⁺ ⟨2, B, C+1, D+2, E⟩ := by
  intro B C D E
  rw [show (2 : ℕ) = 1 + 1 from by ring, show B + 2 = (B + 1) + 1 from by ring]
  step fm
  step fm
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm
  finish

-- k rounds of R1x2R2
theorem r1r1r2_rounds : ∀ k, ∀ C D E, ⟨2, 2*k, C, D, E+k⟩ [fm]⊢* ⟨2, 0, C+k, D+2*k, E⟩ := by
  intro k; induction' k with k h <;> intro C D E
  · exists 0
  rw [show 2 * (k + 1) = (2 * k) + 2 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (r1r1r2_one (2 * k) C D (E + k)))
  have h2 := h (C + 1) (D + 2) E
  rw [show C + 1 + k = C + (k + 1) from by ring,
      show D + 2 + 2 * k = D + 2 * (k + 1) from by ring] at h2
  exact h2

-- Main transition: (d+1, 0, 0, d, 0) →⁺ (2d+2, 0, 0, 2d+1, 0)
theorem main_trans : ⟨d+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2*d+2, 0, 0, 2*d+1, 0⟩ := by
  -- Phase 1: R3 chain (d+1 times): (d+1, 0, 0, d, 0) →* (0, 0, 0, 2d+1, 2d+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 2*d+1, 2*(d+1)⟩)
  · have h := r3_chain (d+1) 0 d 0
    simp only [Nat.zero_add] at h
    rw [show d + (d + 1) = 2 * d + 1 from by ring,
        show 2 * (d + 1) = 2 * (d + 1) from rfl] at h
    exact h
  -- Phase 2: R4 chain (2d+1 times): (0, 0, 0, 2d+1, 2d+2) →* (0, 2d+1, 0, 0, 2d+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*d+1, 0, 0, 2*(d+1)⟩)
  · have h := r4_chain (2*d+1) 0 0 (2*(d+1))
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 3: R5 step: (0, 2d+1, 0, 0, 2d+2) → (1, 2d+1, 0, 0, 2d+1)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2*d+1, 0, 0, 2*d+1⟩)
  · show fm ⟨0, 2*d+1, 0, 0, (2*d+1)+1⟩ = some ⟨1, 2*d+1, 0, 0, 2*d+1⟩
    simp [fm]
  -- Phase 4a: R1 step: (1, 2d+1, 0, 0, 2d+1) → (0, 2d, 1, 1, 2d+1)
  apply stepStar_trans (c₂ := ⟨0, 2*d, 1, 1, 2*d+1⟩)
  · have : ⟨1, 2*d+1, 0, 0, 2*d+1⟩ [fm]⊢ ⟨0, 2*d, 1, 1, 2*d+1⟩ := by
      show fm ⟨0+1, (2*d)+1, 0, 0, 2*d+1⟩ = some ⟨0, 2*d, 1, 1, 2*d+1⟩
      simp [fm]
    exact step_stepStar this
  -- Phase 4b: R2 step: (0, 2d, 1, 1, 2d+1) → (2, 2d, 0, 1, 2d)
  apply stepStar_trans (c₂ := ⟨2, 2*d, 0, 1, 2*d⟩)
  · have : ⟨0, 2*d, 1, 1, 2*d+1⟩ [fm]⊢ ⟨2, 2*d, 0, 1, 2*d⟩ := by
      show fm ⟨0, 2*d, 0+1, 1, (2*d)+1⟩ = some ⟨0+2, 2*d, 0, 1, 2*d⟩
      simp [fm]
    exact step_stepStar this
  -- Phase 4c: d interleaved rounds: (2, 2d, 0, 1, 2d) →* (2, 0, d, 2d+1, d)
  apply stepStar_trans (c₂ := ⟨2, 0, d, 2*d+1, d⟩)
  · have h := r1r1r2_rounds d 0 1 d
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * d = 2 * d + 1 from by ring,
        show d + d = 2 * d from by ring] at h
    exact h
  -- Phase 4d: R2 chain (d times): (2, 0, d, 2d+1, d) →* (2d+2, 0, 0, 2d+1, 0)
  have h := r2_chain d 2 0 (2*d+1)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨d+1, 0, 0, d, 0⟩) 0
  intro d; exact ⟨2*d+1, main_trans⟩
