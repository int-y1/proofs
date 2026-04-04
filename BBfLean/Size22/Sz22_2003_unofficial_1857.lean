import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1857: [9/35, 20/3, 1/20, 343/2, 5/7]

Vector representation:
```
 0  2 -1 -1
 2 -1  1  0
-2  0 -1  0
-1  0  0  3
 0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1857

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a+2, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+3⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | _ => none

-- R4 chain: (a+k, 0, 0, d) →* (a, 0, 0, d+3*k)
theorem r4_chain : ∀ k, ⟨a + k, 0, 0, d⟩ [fm]⊢* ⟨a, 0, 0, d + 3 * k⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (d := d + 3))
    ring_nf; finish

-- Interleaved R1/R2: (a, b, 1, d+k) →* (a+2*k, b+k, 1, d) when d >= 0
theorem interleave : ∀ k, ⟨a, b, 1, d + k⟩ [fm]⊢* ⟨a + 2 * k, b + k, 1, d⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R1: (a, b+2, 0, d+k)
    step fm  -- R2: (a+2, b+1, 1, d+k)
    apply stepStar_trans (ih (a := a + 2) (b := b + 1) (d := d))
    ring_nf; finish

-- R2 drain: (a, b+k, c, 0) →* (a+2*k, b, c+k, 0) when c >= 1
-- Actually we need a version that works when d = 0.
-- R2 fires when b >= 1 (and c can be anything, d can be anything, but R1 has priority when c>=1,d>=1).
-- Here d = 0, so R1 can't fire. R2 fires when b >= 1.
theorem r2_drain : ∀ k, ⟨a, b + k, c, 0⟩ [fm]⊢* ⟨a + 2 * k, b, c + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm  -- R2: (a+2, b+k, c+1, 0)
    apply stepStar_trans (ih (a := a + 2) (b := b) (c := c + 1))
    ring_nf; finish

-- R3 chain: (a+2*k, 0, k, 0) →* (a, 0, 0, 0)
-- R3 fires when a >= 2, c >= 1, b = 0, d = 0
theorem r3_chain : ∀ k, ⟨a + 2 * k, 0, k, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · rw [show a + 2 * (k + 1) = a + 2 * k + 2 from by ring]
    step fm  -- R3: (a+2k, 0, k, 0)
    apply stepStar_trans (ih (a := a))
    finish

-- Main transition: (n+2, 0, 0, 0) ⊢⁺ (6*n+8, 0, 0, 0)
-- Phases:
-- 1. R4 chain (n+2 steps): (n+2, 0, 0, 0) →* (0, 0, 0, 3*n+6)
-- 2. R5: (0, 0, 0, 3*n+6) → (0, 0, 1, 3*n+5)
-- 3. Interleave (3*n+5 pairs): (0, 0, 1, 3*n+5) →* (6*n+10, 3*n+5, 1, 0)
-- 4. R2 drain (3*n+5 steps): (6*n+10, 3*n+5, 1, 0) →* (12*n+20, 0, 3*n+6, 0)
-- 5. R3 chain (3*n+6 steps): (12*n+20, 0, 3*n+6, 0) →* (6*n+8, 0, 0, 0)
theorem main_trans : ⟨n + 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨6 * n + 8, 0, 0, 0⟩ := by
  -- Phase 1: R4 chain
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (n + 2) (a := 0) (d := 0))
  rw [show 0 + 3 * (n + 2) = (3 * n + 5) + 1 from by ring]
  -- Phase 2: R5
  step fm
  -- Phase 3: Interleave
  rw [show (3 * n + 5 : ℕ) = 0 + (3 * n + 5) from by ring]
  apply stepStar_trans (interleave (3 * n + 5) (a := 0) (b := 0) (d := 0))
  rw [show 0 + 2 * (3 * n + 5) = 6 * n + 10 from by ring,
      show 0 + (3 * n + 5) = 3 * n + 5 from by ring]
  -- Phase 4: R2 drain
  rw [show (3 * n + 5 : ℕ) = 0 + (3 * n + 5) from by ring]
  apply stepStar_trans (r2_drain (3 * n + 5) (a := 6 * n + 10) (b := 0) (c := 1))
  rw [show 6 * n + 10 + 2 * (3 * n + 5) = 12 * n + 20 from by ring,
      show 1 + (3 * n + 5) = 3 * n + 6 from by ring]
  -- Phase 5: R3 chain
  rw [show (12 * n + 20 : ℕ) = (6 * n + 8) + 2 * (3 * n + 6) from by ring]
  apply stepStar_trans (r3_chain (3 * n + 6) (a := 6 * n + 8))
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0⟩) 0
  intro n; exact ⟨6 * n + 6, main_trans⟩
