import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #467: [28/15, 21/22, 25/2, 11/7, 21/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  1 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_467

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Phase 1: R3 repeated (b=0, e=0): (a+k, 0, c, d, 0) →* (a, 0, c+2*k, d, 0)
theorem a_to_c : ∀ k, ∀ a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h a (c + 2) d)
  ring_nf; finish

-- Phase 2: R4 repeated (a=0, b=0): (0, 0, c, d+k, e) →* (0, 0, c, d, e+k)
theorem d_to_e : ∀ k, ∀ c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h c d (e + 1))
  ring_nf; finish

-- Phase 3: R2/R1 interleaved chain
-- (A+1, 0, k, D, k) →* (A+1+k, 0, 0, D+2*k, 0)
theorem r2r1_chain : ∀ k, ∀ A D, ⟨A+1, 0, k, D, k⟩ [fm]⊢* ⟨A+1+k, 0, 0, D+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro A D
  · exists 0
  step fm
  step fm
  apply stepStar_trans (h (A+1) (D+2))
  ring_nf; finish

-- Main transition: (a+2, 0, 0, 2*a+2, 0) →⁺ (2*(a+2), 0, 0, 2*(2*a+2)+2, 0)
theorem main_trans (a : ℕ) : ⟨a+2, 0, 0, 2*a+2, 0⟩ [fm]⊢⁺ ⟨2*(a+2), 0, 0, 2*(2*a+2)+2, 0⟩ := by
  -- Phase 1: R3 x (a+2): → (0, 0, 2*(a+2), 2*a+2, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2*(a+2), 2*a+2, 0⟩)
  · have h := a_to_c (a+2) 0 0 (2*a+2)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 x (2*a+2): → (0, 0, 2*(a+2), 0, 2*a+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2*(a+2), 0, 2*a+2⟩)
  · have h := d_to_e (2*a+2) (2*(a+2)) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5
  rw [show 2 * (a + 2) = (2*a+3)+1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 2*a+3, 1, 2*a+2⟩)
  · show fm ⟨0, 0, (2*a+3)+1, 0, 2*a+2⟩ = some ⟨0, 0+1, 2*a+3, 0+1, 2*a+2⟩
    simp [fm]
  -- Phase 4: R1: → (2, 0, 2*a+2, 2, 2*a+2)
  rw [show 2*a+3 = (2*a+2)+1 from by ring]
  apply stepStar_trans (c₂ := ⟨2, 0, 2*a+2, 2, 2*a+2⟩)
  · apply step_stepStar
    show fm ⟨0, 0+1, (2*a+2)+1, 1, 2*a+2⟩ = some ⟨0+2, 0, 2*a+2, 1+1, 2*a+2⟩
    simp [fm]
  -- Phase 5: R2/R1 chain x (2*a+2): → (2*(a+2), 0, 0, 2*(2*a+2)+2, 0)
  have h := r2r1_chain (2*a+2) 1 2
  rw [show (1 : ℕ) + 1 = 2 from rfl,
      show (1 : ℕ) + 1 + (2*a+2) = 2*(a+2) from by ring,
      show 2 + 2*(2*a+2) = 2*(2*a+2)+2 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0+2, 0, 0, 2*0+2, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun a ↦ ⟨a+2, 0, 0, 2*a+2, 0⟩) 0
  intro a
  exact ⟨2*a+2, main_trans a⟩
