import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #80: [1/210, 10/3, 9/55, 7/5, 605/2]

Vector representation:
```
-1 -1 -1 -1  0
 1 -1  1  0  0
 0  2 -1  0 -1
 0  0 -1  1  0
-1  0  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_80

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

-- Drain phase: R5,R3,R2,R1 repeated k+1 times.
-- (a+k+1, 0, 0, k+1, e) ->* (a, 0, 0, 0, e+k+1)
theorem drain_gen :
    ∀ k, ∀ a e, ⟨a+k+1, 0, 0, k+1, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k+1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; step fm; step fm; step fm; ring_nf; finish
  rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
      show (k + 1) + 1 = (k + 1) + 1 from rfl]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3,R2,R2 chain: each round a+=2, c+=1, e-=1.
-- (a, 0, c+1, 0, k+1) ->* (a+2*(k+1), 0, c+k+2, 0, 0)
theorem r3r2r2_chain :
    ∀ k, ∀ a c, ⟨a, 0, c+1, 0, k+1⟩ [fm]⊢* ⟨a+2*(k+1), 0, c+k+2, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · step fm; step fm; step fm; ring_nf; finish
  rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R4 chain: drain c to d.
-- (a, 0, c+k, d, 0) ->* (a, 0, c, d+k, 0)
theorem r4_chain :
    ∀ k, ∀ a c d, ⟨a, 0, c+k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Build-up phase: (a+1, 0, 0, 0, e+1) ->* (a+2*e+6, 0, 0, e+4, 0)
theorem buildup :
    ⟨a+1, 0, 0, 0, e+1⟩ [fm]⊢* ⟨a+2*e+6, 0, 0, e+4, 0⟩ := by
  step fm; step fm; step fm; step fm
  rw [show e + 1 + 1 = (e + 1) + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (e+1) (a+2) 1)
  rw [show a + 2 + 2 * (e + 1 + 1) = a + 2 * e + 6 from by ring,
      show 1 + (e + 1) + 2 = e + 4 from by ring]
  rw [show (e + 4 : ℕ) = 0 + (e + 4) from by ring]
  apply stepStar_trans (r4_chain (e+4) (a+2*e+6) 0 0)
  simp; ring_nf; finish

-- Full transition: (a+d+2, 0, 0, d+1, 0) ->⁺ (a+2*d+6, 0, 0, d+4, 0)
theorem main_trans (a d : ℕ) :
    ⟨a+d+2, 0, 0, d+1, 0⟩ [fm]⊢⁺ ⟨a+2*d+6, 0, 0, d+4, 0⟩ := by
  rw [show a + d + 2 = (a + 1) + d + 1 from by ring]
  -- Use drain_gen to get ⊢*, then convert to ⊢⁺ via stepStar_stepPlus
  have hdrain := drain_gen d (a+1) 0
  simp only [Nat.zero_add] at hdrain
  apply stepStar_stepPlus_stepPlus hdrain
  -- Now at (a+1, 0, 0, 0, d+1). Apply buildup, then one more R5 step to get ⊢⁺.
  -- buildup gives ⊢*. Need ⊢⁺. Start with a step.
  rw [show d + 1 = d + 1 from rfl]
  -- R5 step: (a+1, 0, 0, 0, d+1) -> (a, 0, 1, 0, d+3)
  apply step_stepStar_stepPlus (show ⟨a+1, 0, 0, 0, d+1⟩ [fm]⊢ ⟨a, 0, 1, 0, d+3⟩ from rfl)
  -- R3: (a, 0, 1, 0, d+3) -> (a, 2, 0, 0, d+2)
  step fm
  -- R2: (a, 2, 0, 0, d+2) -> (a+1, 1, 1, 0, d+2)
  step fm
  -- R2: (a+1, 1, 1, 0, d+2) -> (a+2, 0, 2, 0, d+2)
  step fm
  -- R3R2R2 chain (d+2 rounds): need d+2 = (d+1)+1
  rw [show d + 2 = (d + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (d+1) (a+2) 1)
  -- Now at (a+2+2*(d+2), 0, 1+(d+1)+2, 0, 0) = (a+2d+6, 0, d+4, 0, 0)
  rw [show a + 2 + 2 * (d + 1 + 1) = a + 2 * d + 6 from by ring,
      show 1 + (d + 1) + 2 = d + 4 from by ring]
  -- R4 chain
  rw [show (d + 4 : ℕ) = 0 + (d + 4) from by ring]
  apply stepStar_trans (r4_chain (d+4) (a+2*d+6) 0 0)
  simp; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 3, 0⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a+d+2, 0, 0, d+1, 0⟩) ⟨0, 2⟩
  intro ⟨a, d⟩
  refine ⟨⟨a+d+1, d+3⟩, ?_⟩
  show ⟨a+d+2, 0, 0, d+1, 0⟩ [fm]⊢⁺ ⟨(a+d+1)+(d+3)+2, 0, 0, (d+3)+1, 0⟩
  rw [show (a + d + 1) + (d + 3) + 2 = a + 2 * d + 6 from by ring,
      show (d + 3) + 1 = d + 4 from by ring]
  exact main_trans a d

end Sz22_2003_unofficial_80
