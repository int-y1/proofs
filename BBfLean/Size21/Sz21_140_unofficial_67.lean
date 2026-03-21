import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #67: [4/15, 33/14, 275/2, 7/11, 3/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_67

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1+R2 chain: each round (a, 1, c'+1, d'+1, e') → (a+1, 1, c', d', e'+1)
theorem r1r2_chain : ∀ k, ∀ a c d e, ⟨a, 1, c+k, d+k, e⟩ [fm]⊢* ⟨a+k, 1, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R3 chain: a → c, e
theorem r3_chain : ∀ k, ∀ a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 chain: e → d
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: (0, 0, C+2, C+1, 0) →+ (0, 0, 2C+5, 2C+4, 0)
theorem main_trans (C : ℕ) : ⟨0, 0, C+2, C+1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*C+5, 2*C+4, 0⟩ := by
  -- Phase 1: R5
  rw [show C + 2 = (C + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (C + 1) + 1, C + 1, 0⟩ = some ⟨0, 1, C + 1, C + 1, 0⟩
    simp [fm]
  -- Phase 2: R1R2 chain
  apply stepStar_trans (c₂ := ⟨C+1, 1, 0, 0, C+1⟩)
  · have h := @r1r2_chain (C+1) 0 0 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R3 then R1
  apply stepStar_trans (c₂ := ⟨C+2, 0, 1, 0, C+2⟩)
  · rw [show C + 1 = C + 1 from rfl]
    have h1 : ⟨C+1, 1, 0, 0, C+1⟩ [fm]⊢ ⟨C, 1, 2, 0, C+2⟩ := by
      show fm ⟨C + 1, 1, 0, 0, C + 1⟩ = some ⟨C, 1, 2, 0, C + 2⟩
      simp [fm]
    have h2 : ⟨C, 1, 2, 0, C+2⟩ [fm]⊢ ⟨C+2, 0, 1, 0, C+2⟩ := by
      show fm ⟨C, 0 + 1, 1 + 1, 0, C + 2⟩ = some ⟨C + 2, 0, 1, 0, C + 2⟩
      simp [fm]
    exact stepStar_trans (step_stepStar h1) (step_stepStar h2)
  -- Phase 4: R3 chain
  apply stepStar_trans (c₂ := ⟨0, 0, 2*C+5, 0, 2*C+4⟩)
  · have h := @r3_chain (C+2) 0 1 (C+2)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  -- Phase 5: R4 chain
  · have h := @r4_chain (2*C+4) (2*C+5) 0 0
    simp only [Nat.zero_add] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun C ↦ ⟨0, 0, C+2, C+1, 0⟩) 0
  intro C; exact ⟨2*C+3, main_trans C⟩
