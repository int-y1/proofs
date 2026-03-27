import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #69: [1/18, 2/35, 715/2, 147/11, 2/39]

Vector representation:
```
-1 -2  0  0  0  0
 1  0 -1 -1  0  0
-1  0  1  0  1  1
 0  1  0  2 -1  0
 1 -1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_69

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+2, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- Phase A: 9 fixed opening steps
theorem opening : ⟨1, 0, 0, 0, 3*k, 5*k⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, 3*k+1, 5*k+3⟩ := by
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Phase B: R4 chain
theorem r4_chain : ∀ E b d F, ⟨0, b, 0, d, E, F⟩ [fm]⊢* ⟨0, b+E, 0, d+2*E, 0, F⟩ := by
  intro E; induction' E with E ih <;> intro b d F
  · exists 0
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase C: R5/R1 drain
-- (0, 3k+1, 0, D, 0, F+k+1) ->* (1, 0, 0, D, 0, F)
theorem r5r1_chain : ∀ k D F, ⟨0, 3*k+1, 0, D, 0, F+k+1⟩ [fm]⊢* ⟨1, 0, 0, D, 0, F⟩ := by
  intro k; induction' k with k ih <;> intro D F
  · step fm; finish
  -- (0, 3*(k+1)+1, 0, D, 0, F+(k+1)+1) = (0, (3*k+3)+1, 0, D, 0, (F+k+1)+1)
  rw [show 3 * (k + 1) + 1 = (3 * k + 3) + 1 from by ring,
      show F + (k + 1) + 1 = (F + k + 1) + 1 from by ring]
  -- R5: (a, b+1, c, d, e, f+1) -> (a+1, b, c, d, e, f)
  -- matches with b = 3*k+3, f = F+k+1
  step fm
  -- Now at (1, 3*k+3, 0, D, 0, F+k+1)
  -- 3*k+3 = (3*k+1)+2, so R1 fires: (a+1, b+2, ...) -> (a, b, ...)
  rw [show 3 * k + 3 = (3 * k + 1) + 2 from by ring]
  step fm
  -- Now at (0, 3*k+1, 0, D, 0, F+k+1)
  exact ih D F

-- Phase D: R3/R2 chain
theorem r3r2_chain : ∀ D E F, ⟨1, 0, 0, D, E, F⟩ [fm]⊢* ⟨1, 0, 0, 0, E+D, F+D⟩ := by
  intro D; induction' D with D ih <;> intro E F
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Main transition
theorem main_trans (k : ℕ) :
    ⟨1, 0, 0, 0, 3*(k+1), 5*(k+1)⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 3*(2*k+3), 5*(2*k+3)⟩ := by
  -- Phase A
  apply stepPlus_stepStar_stepPlus (opening (k := k+1))
  -- Phase B
  apply stepStar_trans (r4_chain (3*(k+1)+1) 0 1 (5*(k+1)+3))
  -- Phase C
  rw [show 0 + (3 * (k + 1) + 1) = 3 * (k + 1) + 1 from by ring,
      show 1 + 2 * (3 * (k + 1) + 1) = 6*k+9 from by ring,
      show 5 * (k + 1) + 3 = (4*k+6) + (k+1) + 1 from by ring]
  apply stepStar_trans (r5r1_chain (k+1) (6*k+9) (4*k+6))
  -- Phase D
  apply stepStar_trans (r3r2_chain (6*k+9) 0 (4*k+6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 3, 5⟩) (by execute fm 17)
  rw [show (3 : ℕ) = 3 * 1 from by ring, show (5 : ℕ) = 5 * 1 from by ring]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨1, 0, 0, 0, 3*(k+1), 5*(k+1)⟩) 0
  intro k; exists (2*k+2)
  rw [show 2 * k + 2 + 1 = 2 * k + 3 from by ring]
  exact main_trans k

end Sz22_2003_unofficial_69
