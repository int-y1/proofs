import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #45: [1/15, 6/77, 343/3, 5/49, 363/2]

Vector representation:
```
 0 -1 -1  0  0
 1  1  0 -1 -1
 0 -1  0  3  0
 0  0  1 -2  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_45

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R3 drain: convert b to d
theorem r3_drain : ∀ k, ∀ a d, ⟨a, b+k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d+3*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R4 drain: convert d to c
theorem r4_drain : ∀ k, ∀ a c, ⟨a, 0, c, d+2*k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R5+R1 drain: convert a,c to e
theorem r5r1_drain : ∀ k, ∀ a e, ⟨a+k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 2: interleaved R2/R3 from (a, b, 0, 3, 3k+2)
theorem phase2 : ∀ k, ∀ a b, ⟨a, b, 0, 3, 3*k+2⟩ [fm]⊢* ⟨a+3*k+2, b+2*k+2, 0, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · step fm; step fm; ring_nf; finish
  rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 3 from by ring]
  step fm; step fm; step fm
  rw [show a + 3 = a + 3 from rfl]
  rw [show b + 3 = (b + 2) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 5a: 4 fixed steps (requires c >= 1 for R1 in step 4)
theorem phase5a : ⟨a+1, 0, c+2, 1, 0⟩ [fm]⊢* ⟨a+1, 0, c, 0, 1⟩ := by
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Main transition: (1, 0, 0, 0, 3*n) ⊢⁺ (1, 0, 0, 0, 3*(2*n+1))
theorem main_trans (n : ℕ) : ⟨1, 0, 0, 0, 3*n⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 3*(2*n+1)⟩ := by
  -- Phase 1: R5, R3: (1,0,0,0,3n) -> (0,0,0,3,3n+2)
  step fm; step fm
  -- Phase 2: interleaved R2/R3: (0,0,0,3,3n+2) -> (3n+2,2n+2,0,1,0)
  apply stepStar_trans (phase2 n 0 0)
  simp only [Nat.zero_add]
  -- Phase 3: R3 drain: (3n+2,2n+2,0,1,0) -> (3n+2,0,0,6n+7,0)
  rw [show (2*n+2 : ℕ) = 0 + (2*n+2) from by ring]
  apply stepStar_trans (r3_drain (2*n+2) _ _)
  -- Phase 4: R4 drain: (3n+2,0,0,6n+7,0) -> (3n+2,0,3n+3,1,0)
  rw [show (1 + 3*(2*n+2) : ℕ) = 1 + 2*(3*n+3) from by ring]
  apply stepStar_trans (r4_drain (3*n+3) _ _)
  -- Phase 5a: 4 steps: (3n+2,0,3n+3,1,0) -> (3n+2,0,3n+1,0,1)
  rw [show (3*n+2 : ℕ) = (3*n+1)+1 from by ring]
  rw [show (0 + (3*n+3) : ℕ) = (3*n+1)+2 from by ring]
  apply stepStar_trans phase5a
  -- Phase 5b: R5+R1 drain: (3n+2,0,3n+1,0,1) -> (1,0,0,0,6n+3)
  rw [show (3*n+1+1 : ℕ) = 1+(3*n+1) from by ring]
  apply stepStar_trans (r5r1_drain (3*n+1) _ _)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩)
  · exists 0
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, 0, 3*n⟩) 0
  intro n; exact ⟨2*n+1, main_trans n⟩
