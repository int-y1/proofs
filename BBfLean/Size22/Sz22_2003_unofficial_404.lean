import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #404: [225/14, 7/33, 4/3, 11/5, 21/2]

Vector representation:
```
-1  2  2 -1  0
 0 -1  0  1 -1
 2 -1  0  0  0
 0  0 -1  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_404

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c+2, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Rule 4 chain: transfer c to e
theorem c_to_e : ∀ j, ∀ a c e,
    ⟨a, 0, c + j, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + j⟩ := by
  intro j; induction' j with j ih <;> intro a c e
  · exists 0
  rw [show c + (j + 1) = (c + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Rule 2 + Rule 1 pair iterated j times
-- (a+j, b+1, c, 0, e+j) ->* (a, b+j+1, c+2*j, 0, e)
theorem mix_loop : ∀ j, ∀ a b c e,
    ⟨a + j, b + 1, c, 0, e + j⟩ [fm]⊢* ⟨a, b + j + 1, c + 2 * j, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro a b c e
  · simp; exists 0
  rw [show a + (j + 1) = (a + j) + 1 from by ring,
      show e + (j + 1) = (e + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- Rule 3 chain: transfer b to a
theorem b_to_a : ∀ j, ∀ a b c,
    ⟨a, b + j, c, 0, 0⟩ [fm]⊢* ⟨a + 2 * j, b, c, 0, 0⟩ := by
  intro j; induction' j with j ih <;> intro a b c
  · exists 0
  rw [show b + (j + 1) = (b + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Main transition: (a+c+5, 0, c+2, 0, 0) ⊢⁺ (a+2c+11, 0, 2c+6, 0, 0)
theorem main_trans (a c : ℕ) :
    ⟨a + c + 5, 0, c + 2, 0, 0⟩ [fm]⊢⁺ ⟨a + 2 * c + 11, 0, 2 * c + 6, 0, 0⟩ := by
  -- Phase 1: c_to_e (c+2 steps)
  apply stepStar_stepPlus_stepPlus
  · have h := c_to_e (c + 2) (a + c + 5) 0 0
    simp only [(by ring : 0 + (c + 2) = c + 2)] at h
    exact h
  -- Phase 2: rule 5, rule 1 (2 steps)
  apply step_stepPlus_stepPlus
  · show fm ⟨a + c + 5, 0, 0, 0, c + 2⟩ = some ⟨a + c + 4, 1, 0, 1, c + 2⟩; rfl
  apply step_stepStar_stepPlus
  · show fm ⟨a + c + 4, 1, 0, 1, c + 2⟩ = some ⟨a + c + 3, 3, 2, 0, c + 2⟩; rfl
  -- Phase 3: mix_loop (c+2 iterations)
  apply stepStar_trans
  · have h := mix_loop (c + 2) (a + 1) 2 2 0
    simp only [(by ring : (a + 1) + (c + 2) = a + c + 3),
               (by ring : 2 + 1 = 3),
               (by ring : 0 + (c + 2) = c + 2),
               (by ring : 2 + (c + 2) + 1 = c + 5),
               (by ring : 2 + 2 * (c + 2) = 2 * c + 6)] at h
    exact h
  -- Phase 4: rule 3 chain (c+5 steps)
  have h := b_to_a (c + 5) (a + 1) 0 (2 * c + 6)
  simp only [(by ring : 0 + (c + 5) = c + 5),
             (by ring : (a + 1) + 2 * (c + 5) = a + 2 * c + 11)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 2, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + p.2 + 5, 0, p.2 + 2, 0, 0⟩) ⟨0, 0⟩
  intro ⟨a, c⟩
  refine ⟨⟨a + 2, 2 * c + 4⟩, ?_⟩
  show ⟨a + c + 5, 0, c + 2, 0, 0⟩ [fm]⊢⁺ ⟨(a + 2) + (2 * c + 4) + 5, 0, (2 * c + 4) + 2, 0, 0⟩
  rw [show (a + 2) + (2 * c + 4) + 5 = a + 2 * c + 11 from by ring,
      show (2 * c + 4) + 2 = 2 * c + 6 from by ring]
  exact main_trans a c

end Sz22_2003_unofficial_404
