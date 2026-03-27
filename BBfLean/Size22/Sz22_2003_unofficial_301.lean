import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #301: [15/2, 36/35, 1/45, 49/3, 5/7]

Vector representation:
```
-1  1  1  0
 2  2 -1 -1
 0 -2 -1  0
 0 -1  0  2
 0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6

The machine cycles through states (0, 2*(n+1), 0, 0) with n growing as n -> 4*n + 1.
-/

namespace Sz22_2003_unofficial_301

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+1, c+1, d⟩
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+2, b+2, c, d⟩
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | _ => none

-- Phase A: Rule 4 drains b into d.
theorem phaseA : ⟨0, b + k, 0, d⟩ [fm]⊢* ⟨0, b, 0, d + 2*k⟩ := by
  have h : ∀ k b d, ⟨0, b + k, 0, d⟩ [fm]⊢* ⟨0, b, 0, d + 2*k⟩ := by
    intro k; induction' k with k ih <;> intro b d
    · exists 0
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact h k b d

-- Phase B growth loop: rules 2, 1, 1 repeated.
theorem phaseB_growth : ⟨0, b, c + 1, d + k⟩ [fm]⊢* ⟨0, b + 4*k, c + 1 + k, d⟩ := by
  have h : ∀ k b c d, ⟨0, b, c + 1, d + k⟩ [fm]⊢* ⟨0, b + 4*k, c + 1 + k, d⟩ := by
    intro k; induction' k with k ih <;> intro b c d
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish
  exact h k b c d

-- Phase C: Rule 3 loop.
theorem phaseC : ⟨0, b + 2*k, c + k, 0⟩ [fm]⊢* ⟨0, b, c, 0⟩ := by
  have h : ∀ k b c, ⟨0, b + 2*k, c + k, 0⟩ [fm]⊢* ⟨0, b, c, 0⟩ := by
    intro k; induction' k with k ih <;> intro b c
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    exact ih _ _
  exact h k b c

-- Main cycle: (0, 2*(n+1), 0, 0) ->+ (0, 8*n+4, 0, 0)
theorem cycle : ⟨0, 2*(n+1), 0, 0⟩ [fm]⊢⁺ ⟨0, 8*n + 4, 0, 0⟩ := by
  -- Phase A: drain b
  rw [show 2*(n+1) = 0 + (2*(n+1)) from by ring]
  apply stepStar_stepPlus_stepPlus (phaseA (b := 0) (k := 2*(n+1)) (d := 0))
  simp only [Nat.zero_add]
  -- Phase B setup + growth + phase C
  rw [show 2 * (2 * (n + 1)) = (4*n + 2) + 1 + 1 from by ring]
  step fm
  rw [show 4 * n + 2 + 1 = (4 * n + 2) + 1 from by ring]
  step fm; step fm; step fm
  -- Now at (0, 4, 2, 4*n+2)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 4*n + 2 = 0 + (4*n + 2) from by ring]
  apply stepStar_trans (phaseB_growth (b := 4) (c := 1) (d := 0) (k := 4*n+2))
  -- Now at (0, 4+4*(4*n+2), 1+1+(4*n+2), 0) = (0, 16*n+12, 4*n+4, 0)
  rw [show 4 + 4 * (4 * n + 2) = (8*n + 4) + 2*(4*n + 4) from by ring,
      show 1 + 1 + (4 * n + 2) = 0 + (4*n + 4) from by ring]
  exact phaseC (b := 8*n+4) (c := 0) (k := 4*n+4)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0⟩)
  · execute fm 11
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 2*(n+1), 0, 0⟩)
  · intro c ⟨n, hq⟩; subst hq
    refine ⟨⟨0, 8*n+4, 0, 0⟩, ⟨4*n+1, ?_⟩, cycle⟩
    show (0, 8 * n + 4, 0, 0) = (0, 2 * ((4 * n + 1) + 1), 0, 0)
    simp only [Nat.mul_add, Nat.mul_one]; ring_nf
  · exact ⟨0, rfl⟩
