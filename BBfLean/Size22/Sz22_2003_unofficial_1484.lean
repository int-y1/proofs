import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1484: [7/15, 5/231, 726/5, 3/11, 25/2]

Vector representation:
```
 0 -1 -1  1  0
 0 -1  1 -1 -1
 1  1 -1  0  2
 0  1  0  0 -1
-1  0  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1484

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

-- Drain e to b (R4 repeated): (a, b, 0, 0, e+k) →* (a, b+k, 0, 0, e)
theorem e_to_b : ∀ k, ⟨a, b, 0, 0, e + k⟩ [fm]⊢* ⟨a, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R5/R1/R1 one round: (a+1, b+2, 0, d, 0) ⊢⁺ (a, b, 0, d+2, 0)
theorem r5r1r1_step : ⟨a + 1, b + 2, 0, d, 0⟩ [fm]⊢⁺ ⟨a, b, 0, d + 2, 0⟩ := by
  step fm; step fm; step fm; finish

-- R5/R1/R1 chain: (a+k, b+2*k, 0, d, 0) →* (a, b, 0, d+2*k, 0)
theorem r5r1r1 : ∀ k, ⟨a + k, b + 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (a := a + 1) (b := b + 2) (d := d))
    exact stepPlus_stepStar r5r1r1_step

-- R3/R2 spiral: (a, 0, 1, d+k, e) →* (a+k, 0, 1, d, e+k)
theorem spiral : ∀ k, ⟨a, 0, 1, d + k, e⟩ [fm]⊢* ⟨a + k, 0, 1, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R3: (a+1, 1, 0, (d+k)+1, e+2)
    step fm  -- R2: (a+1, 0, 1, d+k, e+1)
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

-- Opening: 5 steps from (a+1, 0, 0, d, 0) to (a+1, 0, 1, d, 0)
-- R5, R3, R1, R4, R2
theorem opening : ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢* ⟨a + 1, 0, 1, d, 0⟩ := by
  step fm  -- R5: (a, 0, 2, d, 0)
  step fm  -- R3: (a+1, 1, 1, d, 2)
  step fm  -- R1: (a+1, 0, 0, d+1, 2)
  step fm  -- R4: (a+1, 1, 0, d+1, 1)
  step fm  -- R2: (a+1, 0, 1, d, 0)
  finish

-- Close spiral and drain: (a, 0, 1, 0, e) →* (a+1, e+3, 0, 0, 0)
theorem close_drain : ⟨a, 0, 1, 0, e⟩ [fm]⊢* ⟨a + 1, e + 3, 0, 0, 0⟩ := by
  step fm  -- R3: (a+1, 1, 0, 0, e+2)
  rw [show e + 2 = 0 + (e + 2) from by ring]
  apply stepStar_trans (e_to_b (e + 2) (a := a + 1) (b := 1) (e := 0))
  ring_nf; finish

-- Odd tail: R5 then R1 from (a+1, 1, 0, d, 0)
theorem odd_tail : ⟨a + 1, 1, 0, d, 0⟩ [fm]⊢* ⟨a, 0, 1, d + 1, 0⟩ := by
  step fm  -- R5: (a, 1, 2, d, 0)
  step fm  -- R1: (a, 0, 1, d+1, 0)
  finish

-- Main transition: (a+1, 0, 0, 2*d, 0) ⊢⁺ (a+2*d+1, 0, 0, 2*d+6, 0)
theorem main_trans : ⟨a + 1, 0, 0, 2 * d, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 1, 0, 0, 2 * d + 6, 0⟩ := by
  -- Phase 1: opening (first step as ⊢⁺)
  apply step_stepStar_stepPlus (by simp [fm] : (⟨a + 1, 0, 0, 2 * d, 0⟩ : Q) [fm]⊢ ⟨a, 0, 2, 2 * d, 0⟩)
  -- Remaining 4 steps of opening
  step fm; step fm; step fm; step fm
  -- Now at (a+1, 0, 1, 2*d, 0)
  -- Phase 2: spiral with k=2*d
  rw [show (2 * d : ℕ) = 0 + 2 * d from by ring]
  apply stepStar_trans (spiral (2 * d) (a := a + 1) (d := 0) (e := 0))
  rw [show a + 1 + 2 * d = a + 2 * d + 1 from by ring,
      show 0 + 2 * d = 2 * d from by ring]
  -- Phase 3: close and drain
  apply stepStar_trans (close_drain (a := a + 2 * d + 1) (e := 2 * d))
  -- Phase 4: r5r1r1 with k=d+1, b leftover = 1
  rw [show a + 2 * d + 1 + 1 = (a + d + 1) + (d + 1) from by ring,
      show 2 * d + 3 = 1 + 2 * (d + 1) from by ring]
  apply stepStar_trans (r5r1r1 (d + 1) (a := a + d + 1) (b := 1) (d := 0))
  rw [show 0 + 2 * (d + 1) = 2 * d + 2 from by ring]
  -- Phase 5: odd tail
  apply stepStar_trans (odd_tail (a := a + d) (d := 2 * d + 2))
  -- Phase 6: spiral with k=2*d+3
  rw [show (2 * d + 3 : ℕ) = 0 + (2 * d + 3) from by ring]
  apply stepStar_trans (spiral (2 * d + 3) (a := a + d) (d := 0) (e := 0))
  rw [show a + d + (2 * d + 3) = a + 3 * d + 3 from by ring,
      show 0 + (2 * d + 3) = 2 * d + 3 from by ring]
  -- Phase 7: close and drain
  apply stepStar_trans (close_drain (a := a + 3 * d + 3) (e := 2 * d + 3))
  -- Phase 8: r5r1r1 with k=d+3, b leftover = 0
  rw [show a + 3 * d + 3 + 1 = (a + 2 * d + 1) + (d + 3) from by ring,
      show 2 * d + 3 + 3 = 0 + 2 * (d + 3) from by ring]
  apply stepStar_trans (r5r1r1 (d + 3) (a := a + 2 * d + 1) (b := 0) (d := 0))
  rw [show 0 + 2 * (d + 3) = 2 * d + 6 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 1, 0, 0, 2 * d, 0⟩) ⟨0, 0⟩
  intro ⟨a, d⟩; exact ⟨⟨a + 2 * d, d + 3⟩, main_trans⟩
