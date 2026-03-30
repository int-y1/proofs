import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1127: [5/6, 44/35, 343/2, 9/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  3  0
 0  2  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1127

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move e to b.
theorem e_to_b : ∀ k b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm  -- R4: (0, b+2, 0, d, k)
    apply stepStar_trans (ih (b + 2) d)
    ring_nf; finish

-- R3 repeated: convert a to d. (a+k, 0, 0, d, e) →* (a, 0, 0, d+3*k, e).
theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (d := d + 3))
    ring_nf; finish

-- R2 repeated (when b=0): convert c,d to a,e.
-- (a, 0, c+k, d+k, e) →* (a+2*k, 0, c, d, e+k).
theorem r2_chain : ∀ k, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (c := c) (d := d) (e := e + 1))
    ring_nf; finish

-- Interleave round: (0, 2*(k+1), c+1, d+1, e) →* (0, 2*k, c+2, d, e+1) in 3 steps.
-- R2: (0, 2*(k+1), c+1, d+1, e) → (2, 2*(k+1), c, d, e+1)
-- R1: (2, 2*(k+1), c, d, e+1) → (1, 2*k+1, c+1, d, e+1)
-- R1: (1, 2*k+1, c+1, d, e+1) → (0, 2*k, c+2, d, e+1)
theorem interleave_round : ⟨0, 2 * (k + 1), c + 1, d + 1, e⟩ [fm]⊢* ⟨0, 2 * k, c + 2, d, e + 1⟩ := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
  step fm  -- R2: (2, (2*k+1)+1, c, d, e+1)
  step fm  -- R1: (1, 2*k+1, c+1, d, e+1)
  -- need 2*k+1 = (2*k) + 1 for second R1
  step fm  -- R1: (0, 2*k, c+2, d, e+1)
  finish

-- Full interleave chain: (0, 2*k, c+1, d+k, e) →* (0, 0, c+k+1, d, e+k).
theorem interleave_chain : ∀ k, ⟨0, 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (interleave_round (k := k) (c := c) (d := d + k) (e := e))
    apply stepStar_trans (ih (c := c + 1) (d := d) (e := e + 1))
    ring_nf; finish

-- Compose phases 3-5: (0, 2*n, 1, 4*n+2, 0) →* (0, 0, 0, 8*n+7, 2*n+1).
theorem phases_345 : ⟨0, 2 * n, 1, 4 * n + 2, 0⟩ [fm]⊢* ⟨0, 0, 0, 8 * n + 7, 2 * n + 1⟩ := by
  -- Phase 3: Interleave
  rw [show 4 * n + 2 = (3 * n + 2) + n from by ring]
  apply stepStar_trans (interleave_chain n (c := 0) (d := 3 * n + 2) (e := 0))
  -- Phase 4: R2 chain
  rw [show 0 + n + 1 = 0 + (n + 1) from by ring,
      show 3 * n + 2 = (2 * n + 1) + (n + 1) from by ring]
  apply stepStar_trans (r2_chain (n + 1) (a := 0) (c := 0) (d := 2 * n + 1) (e := 0 + n))
  -- Phase 5: R3 chain
  rw [show 0 + 2 * (n + 1) = 0 + (2 * n + 2) from by ring,
      show 0 + n + (n + 1) = 2 * n + 1 from by ring]
  apply stepStar_trans (r3_chain (2 * n + 2) (a := 0) (d := 2 * n + 1) (e := 2 * n + 1))
  ring_nf; finish

-- R4 chain specialized: (0, 0, 0, d, n) →* (0, 2*n, 0, d, 0).
theorem e_to_b_zero : ⟨0, 0, 0, d, n⟩ [fm]⊢* ⟨0, 2 * n, 0, d, 0⟩ := by
  have h := e_to_b n 0 d
  simpa using h

-- Phase 1+2: (0, 0, 0, 4*n+3, n) ⊢⁺ (0, 2*n, 1, 4*n+2, 0).
theorem phases_12 : ⟨0, 0, 0, 4 * n + 3, n⟩ [fm]⊢⁺ ⟨0, 2 * n, 1, 4 * n + 2, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_b_zero (d := 4 * n + 3))
  rw [show 4 * n + 3 = (4 * n + 2) + 1 from by ring]
  apply step_stepPlus
  simp [fm]

-- Main transition: (0, 0, 0, 4*n+3, n) ⊢⁺ (0, 0, 0, 8*n+7, 2*n+1).
theorem main_trans : ⟨0, 0, 0, 4 * n + 3, n⟩ [fm]⊢⁺ ⟨0, 0, 0, 8 * n + 7, 2 * n + 1⟩ :=
  stepPlus_stepStar_stepPlus phases_12 phases_345

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 4 * n + 3, n⟩) 0
  intro n; exists (2 * n + 1)
  show ⟨0, 0, 0, 4 * n + 3, n⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * (2 * n + 1) + 3, 2 * n + 1⟩
  rw [show 4 * (2 * n + 1) + 3 = 8 * n + 7 from by ring]
  exact main_trans

end Sz22_2003_unofficial_1127
