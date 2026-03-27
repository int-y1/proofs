import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #549: [28/45, 5/22, 27/2, 11/7, 5/3]

Vector representation:
```
 2 -2 -1  1  0
-1  0  1  0 -1
-1  3  0  0  0
 0  0  0 -1  1
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_549

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 repeated k times
theorem r3_chain : ∀ k b, ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+3*k, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by omega]
  step fm
  apply stepStar_trans (h _); ring_nf; finish

-- R4 repeated k times
theorem d_to_e : ∀ k e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b, 0, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro e
  · ring_nf; finish
  step fm
  apply stepStar_trans (h _); ring_nf; finish

-- R2/R1 alternating: k rounds
theorem r2r1_chain : ∀ k, ∀ a d, ⟨a+1, b+2*k, 0, d, k⟩ [fm]⊢* ⟨a+k+1, b, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · ring_nf; finish
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- Full cycle: (d+2, b, 0, d+1, 0) →⁺ (d+3, b+d+1, 0, d+2, 0)
-- Phase 1: R3 chain d+2 times → (0, b+3d+6, 0, d+1, 0)
-- Phase 2: R4 chain d+1 times → (0, b+3d+6, 0, 0, d+1)
-- Phase 3: R5 → (0, b+3d+5, 1, 0, d+1)
-- Phase 4: R1 → (2, b+3d+3, 0, 1, d+1)
-- Phase 5: R2/R1 chain d+1 times → (d+3, b+d+1, 0, d+2, 0)
-- Check phase 5: a=1, k=d+1, B=b+d+1, d_param=1
--   (2, b+d+1+2*(d+1), 0, 1, d+1) = (2, b+3d+3, 0, 1, d+1) ✓
--   result: (1+(d+1)+1, b+d+1, 0, 1+(d+1), 0) = (d+3, b+d+1, 0, d+2, 0) ✓
theorem main_trans : ⟨d+2, b, 0, d+1, 0⟩ [fm]⊢⁺ ⟨d+3, b+d+1, 0, d+2, 0⟩ := by
  -- Phase 1: R3 chain
  rw [show d + 2 = 0 + (d + 2) from by omega]
  apply stepStar_stepPlus_stepPlus (r3_chain (d+2) b)
  simp only [Nat.zero_add]
  -- Phase 2: R4 chain
  have h2 := @d_to_e (b + 3 * (d + 2)) (d + 1) 0
  simp only [Nat.zero_add] at h2
  apply stepStar_stepPlus_stepPlus h2
  -- Phase 3+4: R5 then R1
  rw [show b + 3 * (d + 2) = (b + d + 1 + 2 * (d + 1)) + 2 + 1 from by ring]
  step fm  -- R5
  step fm  -- R1
  -- Phase 5: R2/R1 chain
  have h5 := @r2r1_chain (b + d + 1) (d + 1) 1 1
  -- h5 : (2, b+d+1+2*(d+1), 0, 1, d+1) ⊢* (1+(d+1)+1, b+d+1, 0, 1+(d+1), 0)
  -- Goal: (2, b+d+1+2*(d+1), 0, 1, d+1) ⊢* (d+3, b+d+1, 0, d+2, 0)
  rw [show (d + 3 : ℕ) = 1 + (d + 1) + 1 from by omega,
      show (d + 2 : ℕ) = 1 + (d + 1) from by omega]
  exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨b, d⟩ ↦ ⟨d+2, b, 0, d+1, 0⟩) ⟨0, 0⟩
  intro ⟨b, d⟩; exact ⟨⟨b+d+1, d+1⟩, main_trans⟩

end Sz22_2003_unofficial_549
