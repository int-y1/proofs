import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1858: [9/35, 20/3, 1/20, 49/2, 3/7]

Vector representation:
```
 0  2 -1 -1
 2 -1  1  0
-2  0 -1  0
-1  0  0  2
 0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1858

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a+2, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R1-R2 spiral: (a, b, 1, k+1) →* (a + 2*(k+1), b + (k+1), 1, 0)
theorem spiral_core : ∀ k, ⟨a, b, 1, k + 1⟩ [fm]⊢* ⟨a + 2 * (k + 1), b + (k + 1), 1, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · step fm; step fm; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a + 2) (b := b + 1))
    ring_nf; finish

-- R2 chain: (a, b, c, 0) →* (a + 2*b, 0, c + b, 0)
theorem r2_chain : ∀ b, ⟨a, b, c, 0⟩ [fm]⊢* ⟨a + 2 * b, 0, c + b, 0⟩ := by
  intro b; induction' b with b ih generalizing a c
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2) (c := c + 1))
    ring_nf; finish

-- R3 chain: (a + 2*k, 0, k, 0) →* (a, 0, 0, 0)
-- R3 fires when a >= 2 and c >= 1: (a+2, 0, c+1, 0) -> (a, 0, c, 0)
-- We use simp [fm] since step fm can't handle symbolic a+2*k.
theorem r3_chain : ∀ k, ⟨a + 2 * k, 0, k, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · have h : fm ⟨a + 2 * (k + 1), 0, k + 1, 0⟩ = some ⟨a + 2 * k, 0, k, 0⟩ := by
      simp [fm]
    exact stepStar_trans (step_stepStar h) ih

-- R4 chain: (k, 0, 0, d) →* (0, 0, 0, d + 2*k)
theorem r4_chain : ∀ k, ⟨k, 0, 0, d⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

-- Full cycle: (0, 0, 0, 2*(n+1)) ⊢⁺ (0, 0, 0, 2*(4*n+2))
theorem main_trans (n : ℕ) : ⟨0, 0, 0, 2 * (n + 1)⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * (4 * n + 2)⟩ := by
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
  -- R5 step
  step fm
  -- R2 step
  step fm
  -- Spiral phase
  rw [show (2 * n + 1 : ℕ) = (2 * n) + 1 from by ring]
  apply stepStar_trans (spiral_core (2 * n) (a := 2) (b := 0))
  rw [show 2 + 2 * (2 * n + 1) = 4 * n + 4 from by ring,
      show 0 + (2 * n + 1) = 2 * n + 1 from by ring]
  -- R2 chain phase
  apply stepStar_trans (r2_chain (2 * n + 1) (a := 4 * n + 4) (c := 1))
  rw [show 4 * n + 4 + 2 * (2 * n + 1) = (4 * n + 2) + 2 * (2 * n + 2) from by ring,
      show 1 + (2 * n + 1) = 2 * n + 2 from by ring]
  -- R3 chain phase
  apply stepStar_trans (r3_chain (2 * n + 2) (a := 4 * n + 2))
  -- R4 chain phase
  apply stepStar_trans (r4_chain (4 * n + 2) (d := 0))
  rw [show 0 + 2 * (4 * n + 2) = 2 * (4 * n + 2) from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * (n + 1)⟩) 0
  intro n; exact ⟨4 * n + 1, main_trans n⟩
