import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1530: [7/30, 2/77, 363/2, 25/11, 14/5]

Vector representation:
```
-1 -1 -1  1  0
 1  0  0 -1 -1
-1  1  0  0  2
 0  0  2  0 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1530

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R2R2R3 chain: (a, b, 0, 2k, 2) →* (a+k, b+k, 0, 0, 2)
-- Each round: R2, R2, R3. Drains d by 2, increments a and b by 1.
theorem r2r2r3_chain : ∀ k a b, ⟨a, b, 0, 2 * k, 2⟩ [fm]⊢* ⟨a + k, b + k, 0, 0, 2⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from rfl]
    step fm
    rw [show 2 * k + 1 = 2 * k + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    -- State: (a+2, b, 0, 2*k, 0). R3 fires (a>=1, c=0 so not R1, e=0 so not R2).
    -- Case split on k to resolve pattern matching on d.
    rcases k with _ | k'
    · -- k=0: state is (a+2, b, 0, 0, 0)
      step fm
      apply stepStar_trans (ih (a + 1) (b + 1))
      ring_nf; finish
    · -- k=k'+1: state is (a+2, b, 0, 2*(k'+1), 0) with d >= 2
      rw [show 2 * (k' + 1) = (2 * k' + 1) + 1 from by ring]
      step fm
      apply stepStar_trans (ih (a + 1) (b + 1))
      ring_nf; finish

-- R3 drain: (j, b, 0, 0, e) →* (0, b+j, 0, 0, e+2*j)
theorem r3_drain : ∀ j b e, ⟨j, b, 0, 0, e⟩ [fm]⊢* ⟨0, b + j, 0, 0, e + 2 * j⟩ := by
  intro j; induction' j with j ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) (e + 2))
    ring_nf; finish

-- R4 chain: (0, b, c, 0, k) →* (0, b, c+2*k, 0, 0)
theorem r4_chain : ∀ k b c, ⟨0, b, c, 0, k⟩ [fm]⊢* ⟨0, b, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  · step fm
    apply stepStar_trans (ih b (c + 2))
    ring_nf; finish

-- R5R1 chain: (0, b+k, c+2k, d, 0) →* (0, b, c, d+2k, 0)
theorem r5r1_chain : ∀ k b c d, ⟨0, b + k + 1, c + 2 * k + 2, d, 0⟩ [fm]⊢* ⟨0, b + 1, c + 2, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + (k + 1) + 1 = (b + k + 1) + 1 from by ring,
        show c + 2 * (k + 1) + 2 = (c + 2 * k + 2) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b c (d + 2))
    ring_nf; finish

-- Main transition: (1, 0, 0, 2d+2, 0) ⊢⁺ (1, 0, 0, 4d+6, 0)
theorem main_trans (d : ℕ) :
    ⟨1, 0, 0, 2 * d + 2, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 4 * d + 6, 0⟩ := by
  -- Phase 1: R3: (1,0,0,2d+2,0) -> (0,1,0,2d+2,2)
  step fm
  -- Phase 2: R2R2R3 chain with k=d+1
  rw [show 2 * d + 2 = 2 * (d + 1) from by ring]
  apply stepStar_trans (r2r2r3_chain (d + 1) 0 1)
  rw [show 0 + (d + 1) = d + 1 from by ring,
      show 1 + (d + 1) = d + 2 from by ring]
  -- State: (d+1, d+2, 0, 0, 2)
  -- Phase 3: R3 drain with j=d+1
  apply stepStar_trans (r3_drain (d + 1) (d + 2) 2)
  rw [show d + 2 + (d + 1) = 2 * d + 3 from by ring,
      show 2 + 2 * (d + 1) = 2 * d + 4 from by ring]
  -- State: (0, 2d+3, 0, 0, 2d+4)
  -- Phase 4: R4 chain with k=2d+4
  apply stepStar_trans (r4_chain (2 * d + 4) (2 * d + 3) 0)
  rw [show 0 + 2 * (2 * d + 4) = 4 * d + 8 from by ring]
  -- State: (0, 2d+3, 4d+8, 0, 0)
  -- Phase 5: R5R1 chain with k=2d+2, b=0, c=2
  rw [show 2 * d + 3 = 0 + (2 * d + 2) + 1 from by ring,
      show 4 * d + 8 = 2 + 2 * (2 * d + 2) + 2 from by ring]
  apply stepStar_trans (r5r1_chain (2 * d + 2) 0 2 0)
  rw [show 0 + 1 = 1 from by ring,
      show 2 + 2 = 4 from by ring,
      show 0 + 2 * (2 * d + 2) = 4 * d + 4 from by ring]
  -- State: (0, 1, 4, 4d+4, 0)
  -- Phase 6: R5: (0, 1, 4, 4d+4, 0) -> (1, 1, 3, 4d+5, 0)
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  step fm
  -- R1: (1, 1, 3, 4d+5, 0) -> (0, 0, 2, 4d+6, 0)
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  -- State: (0, 0, 2, 4d+6, 0)
  -- R5: (0, 0, 2, 4d+6, 0) -> (1, 0, 1, 4d+7, 0)
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  -- R3: (1, 0, 1, 4d+7, 0) -> (0, 1, 1, 4d+7, 2)
  step fm
  -- R2: (0, 1, 1, 4d+7, 2)
  rw [show 4 * d + 7 = (4 * d + 6) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  -- R1: (1, 1, 1, 4d+6, 1)
  step fm
  -- R2: (0, 0, 0, 4d+7, 1)
  rw [show 4 * d + 6 + 1 = (4 * d + 6) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 0⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨1, 0, 0, 2 * d + 2, 0⟩) 0
  intro d
  refine ⟨2 * d + 2, ?_⟩
  rw [show 2 * (2 * d + 2) + 2 = 4 * d + 6 from by ring]
  exact main_trans d

end Sz22_2003_unofficial_1530
