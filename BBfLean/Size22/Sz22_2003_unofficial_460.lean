import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #460: [28/15, 18/7, 1/6, 25/2, 14/5]

Vector representation:
```
 2 -1 -1  1
 1  2  0 -1
-1 -1  0  0
-1  0  2  0
 1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_460

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | _ => none

-- Phase 1: R4 chain: (a+k, 0, c, 0) ⊢* (a, 0, c+2*k, 0)
theorem r4_chain : ∀ k a c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 3: R1,R1,R2 interleaved chain
-- (a, 2, c+2*k, d) ⊢* (a+5*k, 2, c, d+k)
theorem r112_chain : ∀ k a c d, ⟨a, 2, c+2*k, d⟩ [fm]⊢* ⟨a+5*k, 2, c, d+k⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show c + 2 * (k + 1) = c + 2 * k + 1 + 1 from by ring]
  step fm
  rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
  step fm
  rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 5: R2 chain: (a, b, 0, d+k) ⊢* (a+k, b+2*k, 0, d)
theorem r2_chain : ∀ k a b d, ⟨a, b, 0, d+k⟩ [fm]⊢* ⟨a+k, b+2*k, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 6: R3 chain: (a+k, b+k, c, d) ⊢* (a, b, c, d) when c = 0 and d = 0
theorem r3_chain : ∀ k a b, ⟨a+k, b+k, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  finish

-- Phases 1-3: (a+1, 0, 0, 0) ⊢* (5*a+2, 2, 1, a)
theorem to_interleaved_end (a : ℕ) : ⟨a+1, 0, 0, 0⟩ [fm]⊢* ⟨5*a+2, 2, 1, a⟩ := by
  -- Phase 1: R4 chain (a+1 times): (a+1, 0, 0, 0) → (0, 0, 2*a+2, 0)
  rw [show (a : ℕ) + 1 = 0 + (a + 1) from by ring]
  apply stepStar_trans (r4_chain (a+1) 0 0)
  rw [show 0 + 2 * (a + 1) = (2 * a + 1) + 1 from by ring]
  -- Phase 2: R5 then R2: (0, 0, 2*a+2, 0) → (2, 2, 2*a+1, 0)
  step fm; step fm
  -- Phase 3: R1,R1,R2 chain (a rounds): (2, 2, 2*a+1, 0) → (5*a+2, 2, 1, a)
  rw [show 2 * a + 1 = 1 + 2 * a from by ring]
  apply stepStar_trans (r112_chain a 2 1 0)
  ring_nf; finish

-- Phases 4-6: (5*a+2, 2, 1, a) ⊢* (6*a+5, 2*a+3, 0, 0)
theorem interleaved_to_peak : ∀ a : ℕ, ⟨5*a+2, 2, 1, a⟩ [fm]⊢* ⟨6*a+5, 2*a+3, 0, 0⟩ := by
  intro a
  -- R1: b=2>=1, c=1>=1: (5*a+2, 2, 1, a) → (5*a+4, 1, 0, a+1)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- R2: d=a+1>=1: (5*a+4, 1, 0, a+1) → (5*a+5, 3, 0, a)
  step fm
  -- State is now (5*a+2+2+1, 3, 0, a)
  -- R2 chain (a times)
  have key := r2_chain a (5*a+2+2+1) 3 0
  rw [Nat.zero_add] at key
  apply stepStar_trans key
  ring_nf; finish

-- R3 chain from peak: (6*a+5, 2*a+3, 0, 0) ⊢⁺ (4*a+2, 0, 0, 0)
theorem peak_to_next (a : ℕ) : ⟨6*a+5, 2*a+3, 0, 0⟩ [fm]⊢⁺ ⟨4*a+2, 0, 0, 0⟩ := by
  rw [show 6 * a + 5 = (4 * a + 2 + (2 * a + 2)) + 1 from by ring,
      show 2 * a + 3 = (0 + (2 * a + 2)) + 1 from by ring]
  step fm
  apply stepStar_trans (r3_chain (2*a+2) (4*a+2) 0)
  ring_nf; finish

-- Main transition: (a+1, 0, 0, 0) ⊢⁺ (4*a+2, 0, 0, 0)
theorem main_trans (a : ℕ) : ⟨a+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨4*a+2, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (to_interleaved_end a)
  apply stepStar_stepPlus_stepPlus (interleaved_to_peak a)
  exact peak_to_next a

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a, q = ⟨a+1, 0, 0, 0⟩)
  · intro c ⟨a, hq⟩; subst hq
    exact ⟨⟨4*a+2, 0, 0, 0⟩, ⟨4*a+1, by ring_nf⟩, main_trans a⟩
  · exact ⟨0, rfl⟩
