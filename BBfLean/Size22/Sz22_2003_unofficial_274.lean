import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #274: [14/15, 3/154, 25/2, 121/5, 6/11]

Vector representation:
```
 1 -1 -1  1  0
-1  1  0 -1 -1
-1  0  2  0  0
 0  0 -1  0  2
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_274

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- Phase A step: rules 3,1,1: (a+1, b+2, 0, d, 0) →* (a+2, b, 0, d+2, 0)
theorem phase_a_step : ⟨a+1, b+2, 0, d, 0⟩ [fm]⊢* ⟨a+2, b, 0, d+2, 0⟩ := by
  step fm; step fm; step fm; finish

-- Phase A: (a+1, 2*k, 0, d, 0) →* (a+k+1, 0, 0, d+2*k, 0)
theorem phase_a : ⟨a+1, 2*k, 0, d, 0⟩ [fm]⊢* ⟨a+k+1, 0, 0, d+2*k, 0⟩ := by
  induction k generalizing a d with
  | zero => exists 0
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k) + 2 from by ring]
    apply stepStar_trans (phase_a_step (a := a) (b := 2 * k) (d := d))
    rw [show a + 1 + 1 = (a + 1) + 1 from by omega]
    apply stepStar_trans (ih (a := a + 1) (d := d + 2))
    rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by omega,
        show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]
    finish

-- Phase B: rule 3 repeated. (a+j, 0, c, d, 0) →* (a, 0, c+2*j, d, 0)
theorem phase_b : ⟨a+j, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*j, d, 0⟩ := by
  induction j generalizing a c with
  | zero => exists 0
  | succ j ih =>
    rw [show a + (j + 1) = (a + j) + 1 from by omega]
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 2))
    rw [show c + 2 + 2 * j = c + 2 * (j + 1) from by ring]
    finish

-- Phase C: rule 4 repeated, with a=0, b=0. (0, 0, c+j, d, e) →* (0, 0, c, d, e+2*j)
theorem phase_c : ⟨0, 0, c+j, d, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*j⟩ := by
  induction j generalizing c e with
  | zero => exists 0
  | succ j ih =>
    rw [show c + (j + 1) = (c + j) + 1 from by omega]
    step fm
    apply stepStar_trans (ih (c := c) (e := e + 2))
    rw [show e + 2 + 2 * j = e + 2 * (j + 1) from by ring]
    finish

-- Phase D step: rules 5,2: (0, b, 0, d+1, e+2) →* (0, b+2, 0, d, e)
theorem phase_d_step : ⟨0, b, 0, d+1, e+2⟩ [fm]⊢* ⟨0, b+2, 0, d, e⟩ := by
  step fm; step fm; finish

-- Phase D: (0, b, 0, d, e+2*d) →* (0, b+2*d, 0, 0, e)
theorem phase_d : ⟨0, b, 0, d, e+2*d⟩ [fm]⊢* ⟨0, b+2*d, 0, 0, e⟩ := by
  induction d generalizing b e with
  | zero => exists 0
  | succ d ih =>
    rw [show e + 2 * (d + 1) = (e + 2 * d) + 2 from by ring]
    apply stepStar_trans phase_d_step
    apply stepStar_trans (ih (b := b + 2) (e := e))
    rw [show b + 2 + 2 * d = b + 2 * (d + 1) from by ring]
    finish

-- Phase E: 7 steps: (0, b+1, 0, 0, 4) →⁺ (1, b+3, 0, 0, 0)
theorem phase_e : ⟨0, b+1, 0, 0, 4⟩ [fm]⊢⁺ ⟨1, b+3, 0, 0, 0⟩ := by
  execute fm 7

-- Main cycle: (1, 2*(k+1), 0, 0, 0) →⁺ (1, 4*(k+1)+2, 0, 0, 0)
theorem main_cycle (k : ℕ) : ⟨1, 2*(k+1), 0, 0, 0⟩ [fm]⊢⁺ ⟨1, 4*(k+1)+2, 0, 0, 0⟩ := by
  -- Phase A: (1, 2*(k+1), 0, 0, 0) →* (k+2, 0, 0, 2*(k+1), 0)
  rw [show (1 : ℕ) = 0 + 1 from by omega]
  apply stepStar_stepPlus_stepPlus (phase_a (a := 0) (k := k + 1) (d := 0))
  -- Now at (0 + (k+1) + 1, 0, 0, 0 + 2*(k+1), 0) = (k+2, 0, 0, 2k+2, 0)
  -- Phase B: (k+2, 0, 0, 2*(k+1), 0) →* (0, 0, 2*(k+2), 2*(k+1), 0)
  rw [show 0 + (k + 1) + 1 = 0 + (k + 2) from by omega,
      show 0 + 2 * (k + 1) = 2 * (k + 1) from by omega]
  apply stepStar_stepPlus_stepPlus (phase_b (a := 0) (j := k + 2) (c := 0) (d := 2 * (k + 1)))
  -- Now at (0, 0, 0 + 2*(k+2), 2*(k+1), 0)
  -- Phase C: →* (0, 0, 0, 2*(k+1), 4*(k+2))
  apply stepStar_stepPlus_stepPlus (phase_c (c := 0) (j := 2 * (k + 2)) (d := 2 * (k + 1)) (e := 0))
  -- Now at (0, 0, 0, 2*(k+1), 0 + 2*(2*(k+2)))
  -- Phase D: →* (0, 4*(k+1), 0, 0, 4)
  rw [show 0 + 2 * (2 * (k + 2)) = 4 + 2 * (2 * (k + 1)) from by ring,
      show 2 * (k + 1) = 2 * (k + 1) from rfl]
  apply stepStar_stepPlus_stepPlus (phase_d (b := 0) (d := 2 * (k + 1)) (e := 4))
  -- Now at (0, 0 + 2*(2*(k+1)), 0, 0, 4) = (0, 4*(k+1), 0, 0, 4)
  -- Phase E: →⁺ (1, 4*(k+1)+2, 0, 0, 0)
  rw [show 0 + 2 * (2 * (k + 1)) = 4 * k + 3 + 1 from by ring,
      show 4 * (k + 1) + 2 = 4 * k + 3 + 3 from by ring]
  exact phase_e

-- Initial: c₀ →⁺ (1, 2, 0, 0, 0)
theorem init : c₀ [fm]⊢⁺ ⟨1, 2, 0, 0, 0⟩ := by
  execute fm 10

theorem nonhalt : ¬halts fm c₀ := by
  apply stepPlus_not_halts_not_halts init
  apply progress_nonhalt_simple (fm := fm) (C := fun n ↦ ⟨1, 2*(n+1), 0, 0, 0⟩) (i₀ := 0)
  intro n
  exact ⟨2*n+2, by
    rw [show 2 * (2 * n + 2 + 1) = 4 * (n + 1) + 2 from by ring]
    exact main_cycle n⟩
