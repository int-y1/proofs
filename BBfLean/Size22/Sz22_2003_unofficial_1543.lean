import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1543: [7/30, 363/2, 2/77, 25/11, 14/5]

Vector representation:
```
-1 -1 -1  1  0
-1  1  0  0  2
 1  0  0 -1 -1
 0  0  2  0 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1543

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Phase 1: R2-R3 chain.
theorem r2r3_chain : ∀ k b d, ⟨1, b, 0, k + d, b⟩ [fm]⊢* ⟨1, b + k, 0, d, b + k⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · ring_nf; finish
  · rw [show (k + 1) + d = (k + d) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) d); ring_nf; finish

-- Phase 2: R4 chain.
theorem r4_chain : ∀ k b c, ⟨0, b, c, 0, k⟩ [fm]⊢* ⟨0, b, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · ring_nf; finish
  · rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih b (c + 2)); ring_nf; finish

-- Phase 3: R5-R1 chain.
theorem r5r1_chain : ∀ k c d, ⟨0, k, 2 * k + c, d, 0⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show 2 * (k + 1) + c = (2 * k + c + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih c (d + 2)); ring_nf; finish

-- Full transition: (1, 0, 0, d+2, 0) ⊢⁺ (1, 0, 0, 2d+6, 0)
theorem main_trans (d : ℕ) :
    ⟨1, 0, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 2 * d + 6, 0⟩ := by
  -- R2: (1, 0, 0, d+2, 0) -> (0, 1, 0, d+2, 2). This creates the ⊢⁺.
  step fm
  -- R3: (0, 1, 0, d+2, 2) -> (1, 1, 0, d+1, 1)
  rw [show d + 2 = (d + 1) + 1 from by ring,
      show (2 : ℕ) = 0 + 1 + 1 from by ring]
  step fm
  -- R2-R3 chain for d+1 more rounds: (1, 1, 0, d+1, 1) ⊢* (1, d+2, 0, 0, d+2)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show d + 1 = (d + 1) + 0 from by ring]
  apply stepStar_trans (r2r3_chain (d + 1) 1 0)
  rw [show 1 + (d + 1) = d + 2 from by ring]
  -- R2: (1, d+2, 0, 0, d+2) -> (0, d+3, 0, 0, d+4)
  step fm
  rw [show d + 2 + 1 = d + 3 from by ring,
      show d + 2 + 2 = d + 4 from by ring]
  -- Phase 2: R4 chain: (0, d+3, 0, 0, d+4) ⊢* (0, d+3, 2d+8, 0, 0)
  apply stepStar_trans (r4_chain (d + 4) (d + 3) 0)
  -- Phase 3: R5-R1 chain: (0, d+3, 2d+8, 0, 0) ⊢* (0, 0, 2, 2d+6, 0)
  rw [show 0 + 2 * (d + 4) = 2 * (d + 3) + 2 from by ring]
  apply stepStar_trans (r5r1_chain (d + 3) 2 0)
  rw [show 0 + 2 * (d + 3) = 2 * d + 6 from by ring]
  -- Phase 4 tail: (0, 0, 2, 2d+6, 0) -> (1, 0, 0, 2d+6, 0) in 5 steps
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show 2 * d + 6 + 1 = (2 * d + 6) + 1 from by ring,
      show (2 : ℕ) = 0 + 1 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show 2 * d + 6 + 1 = (2 * d + 6) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨1, 0, 0, d + 2, 0⟩) 0
  intro d; exact ⟨2 * d + 4, main_trans d⟩

end Sz22_2003_unofficial_1543
