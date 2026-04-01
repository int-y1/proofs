import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1283: [56/15, 21/22, 65/2, 11/7, 3/13]

Vector representation:
```
 3 -1 -1  1  0  0
-1  1  0  1 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 0  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1283

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+3, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- R4 drain: transfer d to e
theorem d_to_e : ∀ k, ∀ c d e f,
    ⟨(0 : ℕ), (0 : ℕ), c, d + k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c d (e + 1) f)
    ring_nf; finish

-- R3 drain: consume a, add to c and f
theorem r3_drain : ∀ j, ∀ c d f,
    ⟨j, (0 : ℕ), c, d, (0 : ℕ), f⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + j, d, (0 : ℕ), f + j⟩ := by
  intro j; induction' j with j ih <;> intro c d f
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) d (f + 1))
    ring_nf; finish

-- R2+R1 chain: each round consumes 1 from e and 1 from c, adds 2 to a and 2 to d
theorem r2r1_chain : ∀ k, ∀ a c d f,
    ⟨a + 1, (0 : ℕ), c + k, d, k, f⟩ [fm]⊢*
    ⟨a + 2 * k + 1, (0 : ℕ), c, d + 2 * k, (0 : ℕ), f⟩ := by
  intro k; induction' k with k ih <;> intro a c d f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    rw [show a + 3 = (a + 2) + 1 from by ring,
        show d + 1 + 1 = d + 2 from by ring]
    apply stepStar_trans (ih (a + 2) c (d + 2) f)
    ring_nf; finish

-- Main transition: canonical state (0, 0, c+d+2, d+1, 0, f+1) maps to (0, 0, c+2*d+5, 2*d+3, 0, f+2*d+5)
theorem main_trans (c d f : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), c + d + 2, d + 1, (0 : ℕ), f + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), c + 2 * d + 5, 2 * d + 3, (0 : ℕ), f + 2 * d + 5⟩ := by
  -- Phase 1: R4 drain (d+1 steps)
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (d + 1) (c + d + 2) 0 0 (f + 1))
  rw [show 0 + (d + 1) = d + 1 from by ring]
  -- State: (0, 0, c+d+2, 0, d+1, f+1)
  -- Phase 2: R5 (1 step)
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0, c + d + 2, 0, d + 1, f + 1⟩ : Q) [fm]⊢
      ⟨0, 1, c + d + 2, 0, d + 1, f⟩)
  -- State: (0, 1, c+d+2, 0, d+1, f)
  -- Phase 3: R1 (1 step)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show c + d + 2 = (c + d + 1) + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, 0 + 1, (c + d + 1) + 1, 0, d + 1, f⟩ : Q) [fm]⊢
      ⟨3, 0, c + d + 1, 1, d + 1, f⟩))
  -- State: (3, 0, c+d+1, 1, d+1, f)
  -- Phase 4: R2+R1 chain (d+1 rounds)
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show c + d + 1 = c + (d + 1) from by ring,
      show d + 1 = (d + 1 : ℕ) from rfl]
  apply stepStar_trans (r2r1_chain (d + 1) 2 c 1 f)
  -- State: (2+2*(d+1)+1, 0, c, 1+2*(d+1), 0, f) = (2*d+5, 0, c, 2*d+3, 0, f)
  rw [show 2 + 2 * (d + 1) + 1 = 2 * d + 5 from by ring,
      show 1 + 2 * (d + 1) = 2 * d + 3 from by ring]
  -- Phase 5: R3 drain (2*d+5 steps)
  apply stepStar_trans (r3_drain (2 * d + 5) c (2 * d + 3) f)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 1, 0, 3⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨c, d, f⟩ ↦ ⟨0, 0, c + d + 2, d + 1, 0, f + 1⟩) ⟨1, 0, 2⟩
  intro ⟨c, d, f⟩
  refine ⟨⟨c + 1, 2 * d + 2, f + 2 * d + 4⟩, ?_⟩
  show ⟨(0 : ℕ), (0 : ℕ), c + d + 2, d + 1, (0 : ℕ), f + 1⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), (c + 1) + (2 * d + 2) + 2, (2 * d + 2) + 1, (0 : ℕ), (f + 2 * d + 4) + 1⟩
  rw [show (c + 1) + (2 * d + 2) + 2 = c + 2 * d + 5 from by ring,
      show (2 * d + 2) + 1 = 2 * d + 3 from by ring,
      show (f + 2 * d + 4) + 1 = f + 2 * d + 5 from by ring]
  exact main_trans c d f

end Sz22_2003_unofficial_1283
