import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #396: [20/3, 27/35, 1/20, 49/2, 3/7]

Vector representation:
```
 2 -1  1  0
 0  3 -1 -1
-2  0 -1  0
-1  0  0  2
 0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_396

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a, b, c+1, d+1⟩ => some ⟨a, b+3, c, d⟩
  | ⟨a+2, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- Rule 4 repeated: drain a into d
theorem a_to_d : ∀ k, ⟨a+k, 0, 0, d⟩ [fm]⊢* (⟨a, 0, 0, d+2*k⟩ : Q) := by
  intro k; induction k generalizing d with
  | zero => simp; exists 0
  | succ k ih =>
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    exact ih (d := d + 2)

-- Main loop: consume d one at a time
theorem main_loop : ∀ k, ⟨a, 0, c+1, k⟩ [fm]⊢* (⟨a+6*k, 0, c+2*k+1, 0⟩ : Q) := by
  intro k; induction k generalizing a c with
  | zero => simp; exists 0
  | succ k ih =>
    step fm; step fm; step fm; step fm
    rw [show c + 2 * (k + 1) + 1 = (c + 2) + 2 * k + 1 from by ring]
    rw [show a + 6 * (k + 1) = (a + 6) + 6 * k from by ring]
    exact ih (a := a + 6) (c := c + 2)

-- Drain c using rule 3
theorem drain_c : ∀ k, ⟨a+2*k, 0, k, 0⟩ [fm]⊢* (⟨a, 0, 0, 0⟩ : Q) := by
  intro k; induction k generalizing a with
  | zero => simp; exists 0
  | succ k ih =>
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring]
    step fm
    exact ih (a := a)

-- Bootstrap: (0, 0, 0, d+2) ⊢* (8, 0, 3, d)
theorem bootstrap : ⟨0, 0, 0, d+2⟩ [fm]⊢* (⟨8, 0, 3, d⟩ : Q) := by
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm
  rw [show d + 1 = d + 1 from rfl]
  step fm; step fm; step fm; step fm; step fm
  finish

-- Full cycle: from (2*(n+1), 0, 0, 0) to (8*n+6, 0, 0, 0)
theorem cycle (n : ℕ) : (⟨2*(n+1), 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨8*n+6, 0, 0, 0⟩ := by
  -- Phase 1: drain a into d
  rw [show 2*(n+1) = 0 + (2*n+2) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0 + (2 * n + 2), 0, 0, 0⟩ = some _
    rw [show 0 + (2 * n + 2) = (2 * n + 1) + 1 from by ring]
    rfl
  rw [show 2 * n + 1 = 0 + (2 * n + 1) from by ring]
  apply stepStar_trans (a_to_d (2*n+1) (a := 0) (d := 2))
  -- Now at (0, 0, 0, 2+2*(2*n+1)) = (0, 0, 0, 4*n+4)
  rw [show 2 + 2 * (2 * n + 1) = (4 * n + 2) + 2 from by ring]
  apply stepStar_trans (bootstrap (d := 4*n+2))
  -- Now at (8, 0, 3, 4*n+2)
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (main_loop (4*n+2) (a := 8) (c := 2))
  -- Now at (8+6*(4*n+2), 0, 2+2*(4*n+2)+1, 0)
  rw [show 2 + 2 * (4 * n + 2) + 1 = 8 * n + 7 from by ring]
  rw [show 8 + 6 * (4 * n + 2) = (8 * n + 6) + 2 * (8 * n + 7) from by ring]
  exact drain_c (8*n+7) (a := 8*n+6)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (C := fun n ↦ (⟨2*(n+1), 0, 0, 0⟩ : Q)) (i₀ := 0)
  intro n
  refine ⟨4*n+2, ?_⟩
  show (⟨2*(n+1), 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨2*(4*n+2+1), 0, 0, 0⟩
  rw [show 2*(4*n+2+1) = 8*n+6 from by ring]
  exact cycle n

end Sz22_2003_unofficial_396
