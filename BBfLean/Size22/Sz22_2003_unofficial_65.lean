import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #65: [1/18, 175/2, 26/77, 33/5, 2/39]

Vector representation:
```
-1 -2  0  0  0  0
-1  0  2  1  0  0
 1  0  0 -1 -1  1
 0  1 -1  0  1  0
 1 -1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_65

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d+1, e, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- R4 chain: (0, b, c+k, 0, e, f) ⊢* (0, b+k, c, 0, e+k, f)
theorem r4_chain : ∀ k, ∀ b c e f,
    ⟨0, b, c + k, 0, e, f⟩ [fm]⊢* ⟨0, b + k, c, 0, e + k, f⟩ := by
  intro k; induction' k with k h <;> intro b c e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h (b + 1) c (e + 1) f)
  ring_nf; finish

-- R5+R1 drain: (0, 3k+2, 0, 0, e, k+g+1) ⊢* (0, 2, 0, 0, e, g+1)
theorem r5r1_drain : ∀ k, ∀ e g,
    ⟨0, 3*k + 2, 0, 0, e, k + g + 1⟩ [fm]⊢* ⟨0, 2, 0, 0, e, g + 1⟩ := by
  intro k; induction' k with k h <;> intro e g
  · simp; exists 0
  rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 3 from by ring,
      show (k + 1) + g + 1 = (k + g + 1) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h e g)
  ring_nf; finish

-- R2+R3 chain: (1, 1, c, 0, e+k, f) ⊢* (1, 1, c+2*k, 0, e, f+k)
theorem r2r3_chain : ∀ k, ∀ c e f,
    ⟨1, 1, c, 0, e + k, f⟩ [fm]⊢* ⟨1, 1, c + 2*k, 0, e, f + k⟩ := by
  intro k; induction' k with k h <;> intro c e f
  · simp; exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h (c + 2) e (f + 1))
  ring_nf; finish

-- Closing: (1, 1, 2*e, 0, 0, f) ⊢⁺ (0, 0, 2*e+1, 0, 0, f+1)
theorem closing (e f : ℕ) :
    ⟨1, 1, 2*e, 0, 0, f⟩ [fm]⊢⁺ ⟨0, 0, 2*e + 1, 0, 0, f + 1⟩ := by
  step fm
  rw [show 2 * e + 2 = (2 * e + 1) + 1 from by ring]
  step fm; step fm; step fm
  finish

-- Main transition: (0, 0, 3m+2, 0, 0, 2m+2) ⊢⁺ (0, 0, 6m+5, 0, 0, 4m+4)
theorem main_trans (m : ℕ) :
    ⟨0, 0, 3*m + 2, 0, 0, 2*m + 2⟩ [fm]⊢⁺ ⟨0, 0, 6*m + 5, 0, 0, 4*m + 4⟩ := by
  -- Phase 1: R4 chain
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3*m + 2, 0, 0, 3*m + 2, 2*m + 2⟩)
  · have h := r4_chain (3*m + 2) 0 0 0 (2*m + 2)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5+R1 drain (m rounds)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2, 0, 0, 3*m + 2, m + 2⟩)
  · have h := r5r1_drain m (3*m + 2) (m + 1)
    rw [show m + (m + 1) + 1 = 2 * m + 2 from by ring,
        show (m + 1) + 1 = m + 2 from by ring] at h
    exact h
  -- Phase 3: R5 step: (0, 2, 0, 0, 3m+2, m+2) -> (1, 1, 0, 0, 3m+2, m+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 1, 0, 0, 3*m + 2, m + 1⟩)
  · rw [show m + 2 = (m + 1) + 1 from by ring]
    step fm; finish
  -- Phase 4: R2 step: (1, 1, 0, 0, 3m+2, m+1) -> (0, 1, 2, 1, 3m+2, m+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 2, 1, 3*m + 2, m + 1⟩)
  · step fm; finish
  -- Phase 5: R3 step: (0, 1, 2, 1, 3m+2, m+1) -> (1, 1, 2, 0, 3m+1, m+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 1, 2, 0, 3*m + 1, m + 2⟩)
  · rw [show 3 * m + 2 = (3 * m + 1) + 1 from by ring]
    step fm; finish
  -- Phase 6: R2+R3 chain (3m+1 rounds)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 1, 6*m + 4, 0, 0, 4*m + 3⟩)
  · have h := r2r3_chain (3*m + 1) 2 0 (m + 2)
    rw [show 0 + (3 * m + 1) = 3 * m + 1 from by ring,
        show 2 + 2 * (3 * m + 1) = 6 * m + 4 from by ring,
        show (m + 2) + (3 * m + 1) = 4 * m + 3 from by ring] at h
    exact h
  -- Phase 7: Closing
  rw [show 6 * m + 4 = 2 * (3 * m + 2) from by ring,
      show 6 * m + 5 = 2 * (3 * m + 2) + 1 from by ring,
      show 4 * m + 4 = (4 * m + 3) + 1 from by ring]
  exact closing (3*m + 2) (4*m + 3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨0, 0, 3*m + 2, 0, 0, 2*m + 2⟩) 0
  intro m; exact ⟨2*m + 1, by
    show ⟨0, 0, 3*m + 2, 0, 0, 2*m + 2⟩ [fm]⊢⁺ ⟨0, 0, 3*(2*m + 1) + 2, 0, 0, 2*(2*m + 1) + 2⟩
    rw [show 3 * (2 * m + 1) + 2 = 6 * m + 5 from by ring,
        show 2 * (2 * m + 1) + 2 = 4 * m + 4 from by ring]
    exact main_trans m⟩

end Sz22_2003_unofficial_65
