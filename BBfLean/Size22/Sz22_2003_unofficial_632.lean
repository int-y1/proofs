import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #632: [35/6, 143/2, 4/55, 3/7, 18/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_632

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+2, c, d, e, f⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R1R1R3 chain: 3-step rounds consuming b and e, building c and d
theorem r1r1r3_chain : ∀ k, ∀ B C D, ⟨2, B+2*k, C, D, k, F⟩ [fm]⊢* ⟨2, B, C+k, D+2*k, 0, F⟩ := by
  intro k; induction' k with k h <;> intro B C D
  · exists 0
  rw [Nat.mul_succ, ← Nat.add_assoc]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2R2R3 chain: 3-step rounds consuming c, building e and f
theorem r2r2r3_chain : ∀ k, ∀ C E F, ⟨2, 0, C+k, D, E, F⟩ [fm]⊢* ⟨2, 0, C, D, E+k, F+2*k⟩ := by
  intro k; induction' k with k h <;> intro C E F
  · exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: C(n) ->+ C(n+1)
-- C(n) = (0, 0, 0, 2*n+2, n+2, n*n+3*n+3)
theorem main_trans :
    ⟨0, 0, 0, 2*n+2, n+2, n*n+3*n+3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*n+4, n+3, n*n+5*n+7⟩ := by
  -- Phase 1: R4 drain (2n+2 steps)
  rw [show 2*n+2 = 0 + (2*n+2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2*n+2) 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5 (provides the step+)
  rw [show (2*n+2 : ℕ) = (2*n+1) + 1 from by ring]
  rw [show n*n+3*n+3 = (n*n+3*n+2) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Phase 3: R1, R3
  step fm; step fm
  -- Now at (2, 2*n+3, 0, 1, n+1, n*n+3*n+2)
  -- Phase 4: R1R1R3 chain with k=n+1 rounds
  rw [show 2*n+3 = 1 + 2*(n+1) from by ring]
  apply stepStar_trans (r1r1r3_chain (n+1) 1 0 1)
  -- Now at (2, 1, n+1, 1+2*(n+1), 0, n*n+3*n+2) = (2, 1, n+1, 2*n+3, 0, n*n+3*n+2)
  -- Phase 5: R1
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  rw [show 1 + 2*(n+1) = 2*n+3 from by ring]
  step fm
  -- Now at (1, 0, n+2, 2*n+4, 0, n*n+3*n+2)
  -- Phase 6: R2
  step fm
  -- Now at (0, 0, n+2, 2*n+4, 1, n*n+3*n+3)
  -- Phase 7: R3
  step fm
  -- Now at (2, 0, n+1, 2*n+4, 0, n*n+3*n+3)
  -- Phase 8: R2R2R3 chain with k=n+1 rounds
  apply stepStar_trans (r2r2r3_chain (n+1) 0 0 (n*n+3*n+3))
  -- Now at (2, 0, 0, 2*n+4, n+1, n*n+3*n+3+2*(n+1))
  -- Phase 9: R2, R2
  step fm; step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2, 3⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2*n+2, n+2, n*n+3*n+3⟩) 0
  intro n; exists n+1
  show ⟨0, 0, 0, 2*n+2, n+2, n*n+3*n+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*(n+1)+2, (n+1)+2, (n+1)*(n+1)+3*(n+1)+3⟩
  rw [show 2*(n+1)+2 = 2*n+4 from by ring]
  rw [show (n+1)+2 = n+3 from by ring]
  rw [show (n+1)*(n+1)+3*(n+1)+3 = n*n+5*n+7 from by ring]
  exact main_trans

end Sz22_2003_unofficial_632
