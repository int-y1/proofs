import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #419: [27/10, 343/2, 22/21, 5/11, 3/7]

Vector representation:
```
-1  3 -1  0  0
-1  0  0  3  0
 1 -1  0 -1  1
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_419

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase A: paired R3+R1 steps, k iterations
theorem phase_a : ∀ k b d e, ⟨0, b+1, k, d+k, e⟩ [fm]⊢* ⟨0, b+1+2*k, 0, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih (b + 2) d (e + 1))
  ring_nf; finish

-- Phase B: paired R3+R2 steps (c=0), k iterations
theorem phase_b : ∀ k d e, ⟨0, k, 0, d+1, e⟩ [fm]⊢* ⟨0, 0, 0, d+2*k+1, e+k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih (d + 2) (e + 1))
  ring_nf; finish

-- Phase C: convert e to c via rule 4, k iterations
theorem phase_c : ∀ k c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (ih (c + 1) d)
  ring_nf; finish

-- Full cycle as stepStar (starting from after one step)
theorem cycle_star (c m : ℕ) :
    ⟨0, 1, c+1, c+2+m, 0⟩ [fm]⊢* ⟨0, 0, 3*c+4, m+4*c+7, 0⟩ := by
  -- R3: (0, 1, c+1, c+2+m, 0) → (1, 0, c+1, c+1+m, 1)
  rw [show c + 2 + m = (c + 1 + m) + 1 from by ring]
  step fm
  -- R1: (1, 0, c+1, c+1+m, 1) → (0, 3, c, c+1+m, 1)
  step fm
  -- Phase A: c iterations from (0, 3, c, c+1+m, 1) = (0, 2+1, c, (m+1)+c, 1)
  rw [show (3 : ℕ) = 2 + 1 from rfl, show c + 1 + m = (m + 1) + c from by ring]
  apply stepStar_trans (phase_a c 2 (m + 1) 1)
  -- (0, 2+1+2*c, 0, m+1, 1+c) = (0, 2*c+3, 0, m+1, c+1)
  rw [show 2 + 1 + 2 * c = 2 * c + 3 from by ring,
      show 1 + c = c + 1 from by ring]
  -- Phase B: 2*c+3 iterations from (0, 2*c+3, 0, m+1, c+1)
  apply stepStar_trans (phase_b (2 * c + 3) m (c + 1))
  -- (0, 0, 0, m+2*(2*c+3)+1, c+1+(2*c+3)) = (0, 0, 0, m+4*c+7, 3*c+4)
  rw [show m + 2 * (2 * c + 3) + 1 = m + 4 * c + 7 from by ring,
      show c + 1 + (2 * c + 3) = 3 * c + 4 from by ring]
  -- Phase C: 3*c+4 iterations
  apply stepStar_trans (phase_c (3 * c + 4) 0 (m + 4 * c + 7))
  ring_nf; finish

-- Full cycle as stepPlus
theorem cycle (c m : ℕ) :
    ⟨0, 0, c+1, c+3+m, 0⟩ [fm]⊢⁺ ⟨0, 0, 3*c+4, m+4*c+7, 0⟩ := by
  rw [show c + 3 + m = (c + 2 + m) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  exact cycle_star c m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts
  · show c₀ [fm]⊢* (⟨0, 0, 0+1, 0+3+1, 0⟩ : Q)
    unfold c₀; execute fm 5
  apply @progress_nonhalt_simple _ fm (ℕ × ℕ)
    (fun p => (⟨0, 0, p.1+1, p.1+3+p.2, 0⟩ : Q))
    (0, 1)
  intro ⟨c, m⟩
  refine ⟨(3*c+3, m+c+1), ?_⟩
  have h := cycle c m
  show (0, 0, c+1, c+3+m, 0) [fm]⊢⁺ (0, 0, (3*c+3)+1, (3*c+3)+3+(m+c+1), 0)
  rw [show (3*c+3)+1 = 3*c+4 from by ring,
      show (3*c+3)+3+(m+c+1) = m+4*c+7 from by ring]
  exact h

end Sz22_2003_unofficial_419
