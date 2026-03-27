import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #554: [308/15, 1/3, 3/7, 25/2, 1/55, 7/5]

Vector representation:
```
 2 -1 -1  1  1
 0 -1  0  0  0
 0  1  0 -1  0
-1  0  2  0  0
 0  0 -1  0 -1
 0  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_554

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R1/R3 chain with R2 finish: (a, 1, k, 0, e) →* (a+2*k, 0, 0, 0, e+k)
theorem r1r3_chain : ⟨a, 1, k, 0, e⟩ [fm]⊢* ⟨a+2*k, 0, 0, 0, e+k⟩ := by
  have many_step : ∀ k a e, ⟨a, 1, k, 0, e⟩ [fm]⊢* ⟨a+2*k, 0, 0, 0, e+k⟩ := by
    intro k; induction' k with k h <;> intro a e
    · step fm; finish
    · rw [show (k + 1) = k + 1 from rfl]
      step fm; step fm
      apply stepStar_trans (h _ _)
      ring_nf; finish
  exact many_step k a e

-- R4 chain: (a, 0, c, 0, e) →* (0, 0, c+2*a, 0, e)
theorem r4_chain : ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+2*a, 0, e⟩ := by
  have many_step : ∀ a c, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+2*a, 0, e⟩ := by
    intro a; induction' a with a h <;> intro c
    · exists 0
    · step fm
      apply stepStar_trans (h _)
      ring_nf; finish
  exact many_step a c

-- R5 chain: (0, 0, c+k, 0, k) →* (0, 0, c, 0, 0)
theorem r5_chain : ⟨0, 0, c+k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  have many_step : ∀ k c, ⟨0, 0, c+k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
    intro k; induction' k with k h <;> intro c
    · exists 0
    · rw [show c + (k + 1) = (c + k) + 1 from by ring]
      step fm
      apply stepStar_trans (h _)
      ring_nf; finish
  exact many_step k c

-- Main transition: (0, 0, c+2, 0, 0) →⁺ (0, 0, 3*c+3, 0, 0)
theorem main_trans : ⟨0, 0, c+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3*c+3, 0, 0⟩ := by
  step fm; step fm
  apply stepStar_trans (r1r3_chain (a := 0) (k := c+1) (e := 0))
  rw [show 0 + 2 * (c + 1) = 2 * c + 2 from by ring,
      show 0 + (c + 1) = c + 1 from by ring]
  apply stepStar_trans (r4_chain (a := 2*c+2) (c := 0) (e := c+1))
  rw [show 0 + 2 * (2 * c + 2) = 3 * c + 3 + (c + 1) from by ring]
  exact r5_chain

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun c ↦ ⟨0, 0, c+2, 0, 0⟩) 0
  intro c; exists 3*c+1
  rw [show 3 * c + 1 + 2 = 3 * c + 3 from by ring]
  exact main_trans

end Sz22_2003_unofficial_554
