import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #75: [1/18, 35/2, 182/55, 33/7, 2/39]

Vector representation:
```
-1 -2  0  0  0  0
-1  0  1  1  0  0
 1  0 -1  1 -1  1
 0  1  0 -1  1  0
 1 -1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_75

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+1, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- Phase 1: R3 repeated, transfer d to b and e
theorem d_to_be : ∀ k, ∀ b d e, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e+k, f⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2: R4+R0 pairs, drain b and f
theorem r4r0_chain : ∀ k, ∀ b e f, ⟨0, b+3*k, 0, 0, e, f+k⟩ [fm]⊢* ⟨0, b, 0, 0, e, f⟩ := by
  intro k; induction' k with k h <;> intro b e f
  · exists 0
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
      show f + (k + 1) = (f + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 3: R2+R1 interleaved chain
theorem r2r1_chain : ∀ k, ∀ d e f, ⟨0, 1, 1, d, e+k, f⟩ [fm]⊢* ⟨0, 1, 1, d+2*k, e, f+k⟩ := by
  intro k; induction' k with k h <;> intro d e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: (0,0,0,3g+2,0,2g+2) ⊢⁺ (0,0,0,6g+5,0,4g+4)
theorem main_trans (g : ℕ) : ⟨0, 0, 0, 3*g+2, 0, 2*g+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6*g+5, 0, 4*g+4⟩ := by
  -- Phase 1: R3 x (3g+2): (0,0,0,3g+2,0,2g+2) -> (0,3g+2,0,0,3g+2,2g+2)
  have h1 : ⟨0, 0, 0, 3*g+2, 0, 2*g+2⟩ [fm]⊢* ⟨0, 3*g+2, 0, 0, 3*g+2, 2*g+2⟩ := by
    have := d_to_be (3*g+2) 0 0 0 (f := 2*g+2)
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R4+R0 x g: (0,3g+2,0,0,3g+2,2g+2) -> (0,2,0,0,3g+2,g+2)
  have h2 : ⟨0, 3*g+2, 0, 0, 3*g+2, 2*g+2⟩ [fm]⊢* ⟨0, 2, 0, 0, 3*g+2, g+2⟩ := by
    have := r4r0_chain g 2 (3*g+2) (g+2)
    rw [show 2 + 3 * g = 3 * g + 2 from by ring,
        show g + 2 + g = 2 * g + 2 from by ring] at this; exact this
  -- Phase 2b: R4+R1: (0,2,0,0,3g+2,g+2) -> (0,1,1,1,3g+2,g+1)
  have h2b : ⟨0, 2, 0, 0, 3*g+2, g+2⟩ [fm]⊢⁺ ⟨0, 1, 1, 1, 3*g+2, g+1⟩ := by
    rw [show g + 2 = (g + 1) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 3: R2+R1 x (3g+1): (0,1,1,1,3g+2,g+1) -> (0,1,1,6g+3,1,4g+2)
  have h3 : ⟨0, 1, 1, 1, 3*g+2, g+1⟩ [fm]⊢* ⟨0, 1, 1, 6*g+3, 1, 4*g+2⟩ := by
    have := r2r1_chain (3*g+1) 1 1 (g+1)
    rw [show 1 + (3 * g + 1) = 3 * g + 2 from by ring,
        show 1 + 2 * (3 * g + 1) = 6 * g + 3 from by ring,
        show g + 1 + (3 * g + 1) = 4 * g + 2 from by ring] at this; exact this
  -- Phase 3b: R2, R1, R3, R2, R0
  have h3b : ⟨0, 1, 1, 6*g+3, 1, 4*g+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6*g+5, 0, 4*g+4⟩ := by
    rw [show 6 * g + 3 = (6 * g + 2) + 1 from by ring,
        show 4 * g + 2 = (4 * g + 1) + 1 from by ring,
        show 6 * g + 5 = (6 * g + 2) + 1 + 1 + 1 from by ring,
        show 4 * g + 4 = (4 * g + 1) + 1 + 1 + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    step fm  -- R3
    step fm  -- R2
    step fm  -- R0
    ring_nf; finish
  -- Compose all phases
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h2b
        (stepStar_trans h3 (stepPlus_stepStar h3b))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun g ↦ ⟨0, 0, 0, 3*g+2, 0, 2*g+2⟩) 0
  intro g; exists 2*g+1
  have := main_trans g
  rw [show 6 * g + 5 = 3 * (2 * g + 1) + 2 from by ring,
      show 4 * g + 4 = 2 * (2 * g + 1) + 2 from by ring] at this
  exact this
