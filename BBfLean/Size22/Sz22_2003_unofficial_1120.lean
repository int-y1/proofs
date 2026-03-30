import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1120: [5/6, 4/385, 539/2, 3/11, 55/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1 -1
-1  0  0  2  1
 0  1  0  0 -1
 0  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1120

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R3 repeated: drain a into d and e.
-- (a+k, 0, 0, d, e) →* (a, 0, 0, d+2k, e+k)
theorem drain_a : ∀ k, ∀ d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

-- R4 repeated: move e to b.
-- (0, b, 0, d, e+k) →* (0, b+k, 0, d, e)
theorem e_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- Interleaved R5+R2+R1+R1: transfer b to c.
-- (0, b+2k, c, d+2k, 0) →* (0, b, c+2k, d, 0)
theorem interleave :
    ∀ k, ∀ b c d, ⟨0, b + 2 * k, c, d + 2 * k, 0⟩ [fm]⊢* ⟨0, b, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + 2 * (k + 1) = ((b + 2 * k) + 1) + 1 from by ring,
        show d + 2 * (k + 1) = ((d + 2 * k) + 1) + 1 from by ring]
    step fm  -- R5
    step fm  -- R2
    step fm  -- R1
    step fm  -- R1
    apply stepStar_trans (ih b (c + 2) d)
    ring_nf; finish

-- R3+R2 spiral: (a+1, 0, k, d, 0) →* (a+k+1, 0, 0, d+k, 0)
theorem spiral : ∀ k, ∀ a d, ⟨a + 1, 0, k, d, 0⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm  -- R3: (a, 0, k+1, d+2, 1)
    step fm  -- R2: (a+2, 0, k, d+1, 0)
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

-- Main transition: (2a+2, 0, 0, d+1, 0) ⊢⁺ (2a+4, 0, 0, d+4a+3, 0)
theorem main_trans (a d : ℕ) :
    ⟨2 * a + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨2 * a + 4, 0, 0, d + 4 * a + 3, 0⟩ := by
  -- Phase 1: drain a. First R3 step for ⊢⁺.
  rw [show 2 * a + 2 = (2 * a + 1) + 1 from by ring]
  step fm
  -- Now at (2*a+1, 0, 0, d+3, 1), goal is ⊢*
  -- Remaining drain: 2*a+1 more R3 steps
  rw [show 2 * a + 1 = 0 + (2 * a + 1) from by ring]
  apply stepStar_trans (drain_a (2 * a + 1) (d + 3) 1)
  -- Now at (0, 0, 0, d+3+2*(2a+1), 1+(2a+1)) = (0, 0, 0, d+4a+5, 2a+2)
  -- Phase 2: e_to_b
  rw [show 1 + (2 * a + 1) = 0 + (2 * a + 2) from by ring]
  apply stepStar_trans (e_to_b (2 * a + 2) 0 (d + 3 + 2 * (2 * a + 1)))
  -- Now at (0, 2a+2, 0, d+4a+5, 0)
  -- Phase 3: interleave with k = a+1
  rw [show (0 : ℕ) + (2 * a + 2) = 0 + 2 * (a + 1) from by ring,
      show d + 3 + 2 * (2 * a + 1) = (d + 2 * a + 3) + 2 * (a + 1) from by ring]
  apply stepStar_trans (interleave (a + 1) 0 0 (d + 2 * a + 3))
  -- Now at (0, 0, 2a+2, d+2a+3, 0)
  -- Phase 4: R5 + R2
  rw [show (0 : ℕ) + 2 * (a + 1) = 2 * a + 2 from by ring,
      show d + 2 * a + 3 = (d + 2 * a + 2) + 1 from by ring]
  step fm  -- R5: (0, 0, 2a+3, d+2a+2, 1)
  step fm  -- R2: (2, 0, 2a+2, d+2a+1, 0)
  -- Phase 5: spiral with k = 2a+2
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (spiral (2 * a + 2) 1 (d + 2 * a + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨2 * a + 2, 0, 0, d + 1, 0⟩) ⟨0, 0⟩
  intro ⟨a, d⟩
  refine ⟨⟨a + 1, d + 4 * a + 2⟩, ?_⟩
  show ⟨2 * a + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨2 * (a + 1) + 2, 0, 0, (d + 4 * a + 2) + 1, 0⟩
  rw [show 2 * (a + 1) + 2 = 2 * a + 4 from by ring,
      show (d + 4 * a + 2) + 1 = d + 4 * a + 3 from by ring]
  exact main_trans a d

end Sz22_2003_unofficial_1120
