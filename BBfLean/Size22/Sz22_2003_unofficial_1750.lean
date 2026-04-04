import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1750: [9/10, 1/231, 98/3, 11/2, 75/11]

Vector representation:
```
-1  2 -1  0  0
 0 -1  0 -1 -1
 1 -1  0  2  0
-1  0  0  0  1
 0  1  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1750

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+2, d, e⟩
  | _ => none

-- R4 repeated: (a+k, 0, 0, d, e) →* (a, 0, 0, d, e+k)
theorem a_to_e : ∀ k, ∀ e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  · rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (ih (e + 1))
    ring_nf; finish

-- R5/R2 alternation: (0, 0, c, d+k, 2*k+1) →* (0, 0, c+2*k, d, 1)
-- Specialized with the trailing 1.
theorem r5r2_chain : ∀ k, ∀ c d, ⟨0, 0, c, d + k, 2 * k + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, 1⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (c + 2) d)
    ring_nf; finish

-- R1/R3 interleaving: (1, b, j+1, d, 0) →* (1, b+j, 1, d+2*j, 0)
theorem r1r3_chain : ∀ j, ∀ b d, ⟨1, b, j + 1, d, 0⟩ [fm]⊢* ⟨1, b + j, 1, d + 2 * j, 0⟩ := by
  intro j; induction' j with j ih <;> intro b d
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (b + 1) (d + 2))
    ring_nf; finish

-- R3 repeated: (a, b+k, 0, d, 0) →* (a+k, b, 0, d+2*k, 0)
theorem b_to_a : ∀ k, ∀ a d, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a + k, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) (d + 2))
    ring_nf; finish

-- Main transition: (2*k+3, 0, 0, F+k+1, 0) →⁺ (2*k+5, 0, 0, F+8*k+18, 0)
theorem main_trans (k F : ℕ) : ⟨2 * k + 3, 0, 0, F + k + 1, 0⟩ [fm]⊢⁺ ⟨2 * k + 5, 0, 0, F + 8 * k + 18, 0⟩ := by
  -- Phase 1: R4 x (2k+3): →* (0, 0, 0, F+k+1, 2k+3)
  apply stepStar_stepPlus_stepPlus
  · have h := a_to_e (a := 0) (d := F + k + 1) (2 * k + 3) 0
    simp at h; exact h
  -- Phase 2: R5/R2 x (k+1): (0, 0, 0, F+k+1, 2k+3) →* (0, 0, 2k+2, F, 1)
  apply stepStar_stepPlus_stepPlus
  · have h := r5r2_chain (k + 1) 0 F
    rw [show F + (k + 1) = F + k + 1 from by ring,
        show 2 * (k + 1) + 1 = 2 * k + 3 from by ring,
        show 0 + 2 * (k + 1) = 2 * k + 2 from by ring] at h
    exact h
  -- Phase 3a: R5: (0, 0, 2k+2, F, 1) → (0, 1, 2k+4, F, 0)
  -- Phase 3b: R3: (0, 1, 2k+4, F, 0) → (1, 0, 2k+4, F+2, 0)
  -- Phase 4: R1/R3 x (2k+3): (1, 0, 2k+4, F+2, 0) →* (1, 2k+3, 1, F+4k+8, 0)
  -- Phase 4b: R1: (1, 2k+3, 1, F+4k+8, 0) → (0, 2k+5, 0, F+4k+8, 0)
  -- Phase 5: R3 x (2k+5): (0, 2k+5, 0, F+4k+8, 0) →* (2k+5, 0, 0, F+8k+18, 0)
  step fm
  step fm
  rw [show 2 * k + 2 + 2 = (2 * k + 3) + 1 from by ring]
  apply stepStar_trans (r1r3_chain (2 * k + 3) 0 (F + 2))
  step fm
  rw [show 0 + (2 * k + 3) + 2 = 2 * k + 5 from by ring]
  have h := b_to_a (b := 0) (2 * k + 5) 0 (F + 2 + 2 * (2 * k + 3))
  simp at h
  apply stepStar_trans h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 10, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, F⟩ ↦ ⟨2 * k + 3, 0, 0, F + k + 1, 0⟩) ⟨0, 9⟩
  intro ⟨k, F⟩
  refine ⟨⟨k + 1, F + 7 * k + 16⟩, ?_⟩
  show ⟨2 * k + 3, 0, 0, F + k + 1, 0⟩ [fm]⊢⁺ ⟨2 * (k + 1) + 3, 0, 0, (F + 7 * k + 16) + (k + 1) + 1, 0⟩
  rw [show 2 * (k + 1) + 3 = 2 * k + 5 from by ring,
      show (F + 7 * k + 16) + (k + 1) + 1 = F + 8 * k + 18 from by ring]
  exact main_trans k F

end Sz22_2003_unofficial_1750
