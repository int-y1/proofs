import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #481: [28/15, 3/22, 125/2, 121/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  3  0  0
 0  0  0 -1  2
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_481

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 chain: (a+k, 0, C, D, 0) →* (a, 0, C+3*k, D, 0)
theorem r3_chain : ∀ k, ∀ a C D, ⟨a+k, 0, C, D, 0⟩ [fm]⊢* ⟨a, 0, C+3*k, D, 0⟩ := by
  intro k; induction' k with k h <;> intro a C D
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R4 chain: (0, 0, C, D+k, E) →* (0, 0, C, D, E+2*k)
theorem r4_chain : ∀ k, ∀ C D E, ⟨0, 0, C, D+k, E⟩ [fm]⊢* ⟨0, 0, C, D, E+2*k⟩ := by
  intro k; induction' k with k h <;> intro C D E
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- (R2, R1) chain: (a+1, 0, C+k, D, k) →* (a+k+1, 0, C, D+k, 0)
theorem r2r1_chain : ∀ k, ∀ a C D, ⟨a+1, 0, C+k, D, k⟩ [fm]⊢* ⟨a+k+1, 0, C, D+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a C D
  · exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring,
      show (k : ℕ) + 1 = k + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (h (a+1) _ _); ring_nf; finish

-- R5 then R1: (0, 0, C+2, 0, E) →* (2, 0, C, 1, E)
theorem r5_r1 : ∀ C E, ⟨0, 0, C+2, 0, E⟩ [fm]⊢* ⟨2, 0, C, 1, E⟩ := by
  intro C E
  apply stepStar_trans (c₂ := ⟨0, 1, C+1, 0, E⟩)
  · apply step_stepStar
    show fm ⟨0, 0, (C+1)+1, 0, E⟩ = some ⟨0, 1, C+1, 0, E⟩
    simp [fm]
  apply step_stepStar
  show fm ⟨0, 0+1, (C)+1, 0, E⟩ = some ⟨0+2, 0, C, 0+1, E⟩
  simp [fm]

-- Main transition: (d+1, 0, d, d, 0) →⁺ (2*d+2, 0, 2*d+1, 2*d+1, 0)
theorem main_trans : ⟨d+1, 0, d, d, 0⟩ [fm]⊢⁺ ⟨2*d+2, 0, 2*d+1, 2*d+1, 0⟩ := by
  -- Phase 1: one R3 step: (d+1, 0, d, d, 0) → (d, 0, d+3, d, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨d+1, 0, d, d, 0⟩ = some ⟨d, 0, d+3, d, 0⟩
    simp [fm]
  -- Phase 1b: R3 x d more: (d, 0, d+3, d, 0) →* (0, 0, d+3+3*d, d, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, d+3+3*d, d, 0⟩)
  · have h := r3_chain d 0 (d+3) d; simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 x d: →* (0, 0, d+3+3*d, 0, 2*d)
  apply stepStar_trans (c₂ := ⟨0, 0, d+3+3*d, 0, 2*d⟩)
  · have h := r4_chain d (d+3+3*d) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5, R1: →* (2, 0, d+3*d+1, 1, 2*d)
  apply stepStar_trans (c₂ := ⟨2, 0, d+3*d+1, 1, 2*d⟩)
  · have h := r5_r1 (d+3*d+1) (2*d)
    rw [show d + 3 * d + 1 + 2 = d + 3 + 3 * d from by ring] at h; exact h
  -- Phase 4: (R2, R1) x 2d: →* (2d+2, 0, 2d+1, 2d+1, 0)
  rw [show d + 3 * d + 1 = (2*d+1) + 2*d from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show (1 : ℕ) = 1 from rfl]
  have h := r2r1_chain (2*d) 1 (2*d+1) 1
  rw [show 1 + 2 * d + 1 = 2 * d + 2 from by ring,
      show 1 + 2 * d = 2 * d + 1 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3+1, 0, 3, 3, 0⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨d+1, 0, d, d, 0⟩) 3
  intro d; exact ⟨2*d+1, main_trans⟩
