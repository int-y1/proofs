import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #66: [4/15, 33/14, 275/2, 7/11, 2/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 1  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_66

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- Phase 1: R3 repeated: (a+k, 0, c, 0, e) →* (a, 0, c+2*k, 0, e+k)
theorem r3_chain : ∀ k, ∀ a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2: R4 repeated: (0, 0, c, d, e+k) →* (0, 0, c, d+k, e)
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 4: R2+R1 interleaved: (a+1, 0, c+k, d+k, e) →* (a+1+k, 0, c, d, e+k)
theorem r2r1_chain : ∀ k, ∀ a c d e, ⟨a+1, 0, c+k, d+k, e⟩ [fm]⊢* ⟨a+1+k, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Main transition: (e+1, 0, 0, 0, e) ⊢⁺ (2e+2, 0, 0, 0, 2e+1)
theorem main_trans : ⟨e+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨2*e+2, 0, 0, 0, 2*e+1⟩ := by
  -- Phase 1: R3 chain: (e+1, 0, 0, 0, e) →* (0, 0, 2e+2, 0, 2e+1)
  have h1 : ⟨e+1, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2*e+2, 0, 2*e+1⟩ := by
    have := r3_chain (e+1) 0 0 e
    simp only [Nat.zero_add] at this
    refine stepStar_trans this ?_
    ring_nf; finish
  -- Phase 2: R4 chain: (0, 0, 2e+2, 0, 2e+1) →* (0, 0, 2e+2, 2e+1, 0)
  have h2 : ⟨0, 0, 2*e+2, 0, 2*e+1⟩ [fm]⊢* ⟨0, 0, 2*e+2, 2*e+1, 0⟩ := by
    have := r4_chain (2*e+1) (2*e+2) 0 0
    simp only [Nat.zero_add] at this
    refine stepStar_trans this ?_
    ring_nf; finish
  -- Phase 3: R5 step: (0, 0, 2e+2, 2e+1, 0) → (1, 0, 2e+1, 2e+1, 0)
  have h3 : ⟨0, 0, 2*e+2, 2*e+1, 0⟩ [fm]⊢ ⟨1, 0, 2*e+1, 2*e+1, 0⟩ := by
    show fm ⟨0, 0, (2*e+1)+1, 2*e+1, 0⟩ = some ⟨0+1, 0, 2*e+1, 2*e+1, 0⟩
    simp [fm]
  -- Phase 4: R2+R1 chain: (1, 0, 2e+1, 2e+1, 0) →* (2e+2, 0, 0, 0, 2e+1)
  have h4 : ⟨1, 0, 2*e+1, 2*e+1, 0⟩ [fm]⊢* ⟨2*e+2, 0, 0, 0, 2*e+1⟩ := by
    have := r2r1_chain (2*e+1) 0 0 0 0
    simp only [Nat.zero_add] at this
    refine stepStar_trans this ?_
    ring_nf; finish
  -- Compose: h1 (⊢*), h2 (⊢*), h3 (⊢), h4 (⊢*) → ⊢⁺
  apply stepStar_stepPlus_stepPlus h1
  apply stepPlus_stepStar_stepPlus (stepStar_step_stepPlus h2 h3)
  exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun e ↦ ⟨e+1, 0, 0, 0, e⟩) 0
  intro e; exact ⟨2*e+1, main_trans⟩
