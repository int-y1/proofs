import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #530: [28/15, 39/22, 35/2, 11/13, 33/7]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  1
-1  0  1  1  0  0
 0  0  0  0  1 -1
 0  1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_530

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

-- R4 repeated: convert f to e
theorem f_to_e (c d : ℕ) : ⟨0, 0, c, d, e, k⟩ [fm]⊢* ⟨0, 0, c, d, e+k, 0⟩ := by
  have many_step : ∀ k e, ⟨0, 0, c, d, e, k⟩ [fm]⊢* ⟨0, 0, c, d, e+k, 0⟩ := by
    intro k; induction' k with k h <;> intro e
    · exists 0
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k e

-- R3 repeated: drain a, building c and d
theorem a_drain (f : ℕ) : ⟨k, 0, c, d, 0, f⟩ [fm]⊢* ⟨0, 0, c+k, d+k, 0, f⟩ := by
  have many_step : ∀ k c d, ⟨k, 0, c, d, 0, f⟩ [fm]⊢* ⟨0, 0, c+k, d+k, 0, f⟩ := by
    intro k; induction' k with k h <;> intro c d
    · exists 0
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c d

-- R1/R2 interleaved chain
theorem r1r2_chain : ⟨a, 1, c+k, d, k, f⟩ [fm]⊢* ⟨a+k, 1, c, d+k, 0, f+k⟩ := by
  have many_step : ∀ k, ∀ a c d f, ⟨a, 1, c+k, d, k, f⟩ [fm]⊢* ⟨a+k, 1, c, d+k, 0, f+k⟩ := by
    intro k; induction' k with k h <;> intro a c d f
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (h _ _ _ _)
    ring_nf; finish
  exact many_step k a c d f

-- R5 step
theorem r5_step (c d e : ℕ) : ⟨0, 0, c, d+1, e, 0⟩ [fm]⊢ ⟨0, 1, c, d, e+1, 0⟩ := by
  simp [fm]

-- Main transition
theorem main_trans : ⟨0, 0, n+1, D+1, 0, n⟩ [fm]⊢⁺ ⟨0, 0, n+2, D+2*n+5, 0, n+1⟩ := by
  -- Phase 1: f_to_e
  rw [show (0 : ℕ) = 0 + 0 from by ring]
  apply stepStar_stepPlus_stepPlus (f_to_e (n+1) (D+1))
  simp only [Nat.zero_add]
  -- Phase 2: R5
  apply step_stepStar_stepPlus (r5_step (n+1) D n)
  -- Phase 3: R1/R2 chain
  have h3 : ⟨0, 1, 0+(n+1), D, n+1, 0⟩ [fm]⊢* ⟨0+(n+1), 1, 0, D+(n+1), 0, 0+(n+1)⟩ := r1r2_chain
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  -- Phase 4: R3
  step fm
  -- Phase 5: R1
  step fm
  -- Phase 6: a_drain
  have h6 : ⟨n+2, 0, 0, D+(n+1)+1+1, 0, n+1⟩ [fm]⊢* ⟨0, 0, 0+(n+2), (D+(n+1)+1+1)+(n+2), 0, n+1⟩ :=
    a_drain (n+1)
  apply stepStar_trans h6
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 1, 0, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n+1, n*n+3*n+1, 0, n⟩) 0
  intro n
  refine ⟨n+1, ?_⟩
  rw [show n * n + 3 * n + 1 = (n * n + 3 * n) + 1 from by ring]
  rw [show (n + 1) * (n + 1) + 3 * (n + 1) + 1 = (n * n + 3 * n) + 2 * n + 5 from by ring]
  exact main_trans

end Sz22_2003_unofficial_530
