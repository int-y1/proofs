import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #790: [35/6, 605/2, 20/77, 3/5, 7/3]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  1 -1 -1
 0  1 -1  0  0
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_790

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: move c to b (when a=0, d=0).
theorem c_to_b : ∀ k b e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro b e; exists 0
  · intro b e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e); ring_nf; finish

-- One R3,R1,R1 round: (0, b+2, c, d+1, e+1) ⊢* (0, b, c+3, d+2, e).
theorem r3r1r1_round : ⟨0, b + 2, c, d + 1, e + 1⟩ [fm]⊢* ⟨0, b, c + 3, d + 2, e⟩ := by
  step fm; step fm; step fm; finish

-- Spiral chain: k rounds of R3,R1,R1.
-- (0, 2*k, c, d+1, e+k) ⊢* (0, 0, c+3*k, d+k+1, e)
theorem spiral_chain : ∀ k c d e, ⟨0, 2 * k, c, d + 1, e + k⟩ [fm]⊢* ⟨0, 0, c + 3 * k, d + k + 1, e⟩ := by
  intro k; induction' k with k ih
  · intro c d e; exists 0
  · intro c d e
    rw [show 2 * (k + 1) = (2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans r3r1r1_round
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 3) (d + 1) e)
    ring_nf; finish

-- Drain chain: rounds of R3,R2,R2.
-- (0, 0, c, d, e+1) ⊢* (0, 0, c+3*d, 0, e+1+3*d)
theorem drain_chain : ∀ d c e, ⟨0, 0, c, d, e + 1⟩ [fm]⊢* ⟨0, 0, c + 3 * d, 0, e + 1 + 3 * d⟩ := by
  intro d; induction' d with d ih
  · intro c e; exists 0
  · intro c e
    step fm; step fm; step fm
    rw [show e + 4 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (c + 3) (e + 3))
    ring_nf; finish

-- Main transition: (0, 0, 2*k+1, 0, e+k+1) ⊢⁺ (0, 0, 6*k+3, 0, e+3*k+4).
theorem main_trans (k e : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, e + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 6 * k + 3, 0, e + 3 * k + 4⟩ := by
  -- Phase 1: c_to_b
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (c_to_b (2 * k + 1) 0 (e + k + 1) (c := 0))
  rw [show 0 + (2 * k + 1) = 2 * k + 1 from by ring]
  -- Phase 2: R5 step
  apply step_stepStar_stepPlus
  · show ⟨0, 2 * k + 1, 0, 0, e + k + 1⟩ [fm]⊢ ⟨0, 2 * k, 0, 1, e + k + 1⟩
    simp [fm]
  -- Phase 3: spiral chain
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show e + k + 1 = (e + 1) + k from by ring]
  apply stepStar_trans (spiral_chain k 0 0 (e + 1))
  rw [show 0 + 3 * k = 3 * k from by ring,
      show 0 + k + 1 = k + 1 from by ring]
  -- Phase 4: drain chain
  apply stepStar_trans (drain_chain (k + 1) (3 * k) e)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 2 * p.1 + 1, 0, p.2 + p.1 + 1⟩) ⟨0, 1⟩
  intro ⟨k, e⟩
  refine ⟨⟨3 * k + 1, e + 2⟩, ?_⟩
  show ⟨0, 0, 2 * k + 1, 0, e + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 2 * (3 * k + 1) + 1, 0, (e + 2) + (3 * k + 1) + 1⟩
  rw [show 2 * (3 * k + 1) + 1 = 6 * k + 3 from by ring,
      show (e + 2) + (3 * k + 1) + 1 = e + 3 * k + 4 from by ring]
  exact main_trans k e

end Sz22_2003_unofficial_790
