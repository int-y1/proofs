import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #142: [1/45, 20/3, 3/14, 11/2, 441/11]

Vector representation:
```
 0 -2 -1  0  0
 2 -1  1  0  0
-1  1  0 -1  0
-1  0  0  0  1
 0  2  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_142

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+2, e⟩
  | _ => none

-- Phase 1: R4 repeated. Drain a to e.
theorem drain_a : ∀ k e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  · step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- Phase 2: R5+R1 repeated. Convert c to d, consuming e.
theorem peel_c : ∀ k d e, ⟨0, 0, k, d, e + k⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · simp; exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Phase 3: R3+R2 repeated. Convert d to a and c. Requires a >= 1.
theorem r3r2_loop : ∀ k a c' e, ⟨a + 1, 0, c', k, e⟩ [fm]⊢* ⟨a + 1 + k, 0, c' + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c' e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Main transition: C(c, e) = (c+2, 0, c, 0, e) ⊢⁺ C(2c+4, e+1) = (2c+6, 0, 2c+4, 0, e+1)
theorem main_trans (c e : ℕ) :
    ⟨c + 2, 0, c, 0, e⟩ [fm]⊢⁺ ⟨(2 * c + 4) + 2, 0, 2 * c + 4, 0, e + 1⟩ := by
  -- Phase 1: drain a = c+2 to e
  apply stepStar_stepPlus_stepPlus (drain_a (c + 2) e)
  -- Now at (0, 0, c, 0, e + (c + 2))
  -- Phase 2: peel c, converting to d
  rw [show e + (c + 2) = (e + 2) + c from by ring]
  apply stepStar_stepPlus_stepPlus (peel_c c 0 (e + 2))
  -- Now at (0, 0, 0, 2c, e + 2)
  simp only [Nat.zero_add]
  -- Phase 3: R5 step
  rw [show e + 2 = (e + 1) + 1 from by ring]
  step fm
  -- Now at (0, 2, 0, 2c+2, e+1)
  -- Phase 4: R2 + R2
  step fm; step fm
  -- Now at (4, 0, 2, 2c+2, e+1)
  -- Phase 5: R3+R2 loop with d = 2c+2
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r3r2_loop (2 * c + 2) 3 2 (e + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨6, 0, 4, 0, 0⟩)
  · execute fm 8
  · exact progress_nonhalt_simple (A := ℕ × ℕ)
      (C := fun ⟨c, e⟩ ↦ (⟨c + 2, 0, c, 0, e⟩ : Q))
      (i₀ := ⟨4, 0⟩)
      (fun ⟨c, e⟩ ↦ ⟨⟨2 * c + 4, e + 1⟩, main_trans c e⟩)
