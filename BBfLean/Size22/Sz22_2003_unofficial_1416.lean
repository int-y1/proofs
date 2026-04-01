import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1416: [7/15, 121/3, 6/77, 25/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 0 -1  0  0  2
 1  1  0 -1 -1
 0  0  2  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1416

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Phase 2: R3+R2 chain. Each round: (a, 0, 0, D, e+1) with D≥1
-- does R3 then R2, yielding (a+1, 0, 0, D-1, e+2).
-- After k rounds: (a+k, 0, 0, 0, e+k+1).
theorem r3r2_chain : ∀ k a e, ⟨a, 0, 0, k, e + 1⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl,
        show e + (k + 1) + 1 = (e + 1) + k + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- Phase 3: R4 chain converting e to c (odd e case).
-- (a, 0, c, 0, 2k+1) →* (a, 0, c+2k, 0, 1)
theorem r4_chain : ∀ k a c, ⟨a, 0, c, 0, 2 * k + 1⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, 1⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2))
    ring_nf; finish

-- Phase 5: R5+R1 chain.
-- (a+k, 0, c+k, D, 0) →* (a, 0, c, D+2k, 0)
theorem r5r1_chain : ∀ k a c D, ⟨a + k, 0, c + k, D, 0⟩ [fm]⊢* ⟨a, 0, c, D + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c D
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c (D + 2))
    ring_nf; finish

-- Main transition: (1, 0, 0, 2n+2, 0) ⊢⁺ (1, 0, 0, 4n+6, 0)
theorem main_trans (n : ℕ) :
    ⟨1, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 4 * n + 6, 0⟩ := by
  -- Phase 1: R5 + R2: (1, 0, 0, 2n+2, 0) → (0, 1, 0, 2n+3, 0) → (0, 0, 0, 2n+3, 2)
  step fm; step fm
  -- Phase 2: R3+R2 chain, 2n+3 rounds:
  -- (0, 0, 0, 2n+3, 2) →* (2n+3, 0, 0, 0, 2n+5)
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r3r2_chain (2 * n + 3) 0 1)
  rw [show 0 + (2 * n + 3) = 2 * n + 3 from by ring,
      show 1 + (2 * n + 3) + 1 = 2 * n + 5 from by ring,
      show 2 * n + 5 = 2 * (n + 2) + 1 from by ring]
  -- Phase 3: R4 chain, n+2 times:
  -- (2n+3, 0, 0, 0, 2(n+2)+1) →* (2n+3, 0, 2n+4, 0, 1)
  apply stepStar_trans (r4_chain (n + 2) (2 * n + 3) 0)
  rw [show 0 + 2 * (n + 2) = 2 * n + 4 from by ring]
  -- Phase 4: 4 fixed steps
  -- (2n+3, 0, 2n+4, 0, 1) → R5 → (2n+2, 1, 2n+4, 1, 1)
  -- → R1 → (2n+2, 0, 2n+3, 2, 1) → R3 → (2n+3, 1, 2n+3, 1, 0)
  -- → R1 → (2n+3, 0, 2n+2, 2, 0)
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring,
      show 2 * n + 4 = (2 * n + 3) + 1 from by ring]
  step fm; step fm
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
  step fm; step fm
  -- Phase 5: R5+R1 chain, 2n+2 rounds:
  -- (2n+3, 0, 2n+2, 2, 0) →* (1, 0, 0, 4n+6, 0)
  have phase5 := r5r1_chain (2 * n + 2) 1 0 2
  rw [show 1 + (2 * n + 2) = 2 * n + 3 from by ring,
      show 0 + (2 * n + 2) = 2 * n + 2 from by ring,
      show 2 + 2 * (2 * n + 2) = 4 * n + 6 from by ring] at phase5
  exact phase5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 0⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, 2 * n + 2, 0⟩) 0
  intro n; refine ⟨2 * n + 2, ?_⟩
  rw [show 2 * (2 * n + 2) + 2 = 4 * n + 6 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1416
