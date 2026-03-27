import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #5: [1/105, 2/3, 45/22, 49/2, 363/7]

Vector representation:
```
 0 -1 -1 -1  0
 1 -1  0  0  0
-1  2  1  0 -1
-1  0  0  2  0
 0  1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_5

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- Phase 1: R3/R2/R2 chain.
-- From (a+1, 0, c, 0, k) to (a+k+1, 0, c+k, 0, 0) in 3*k steps.
theorem phase1 : ∀ k : ℕ, ∀ a c,
    ⟨a + 1, 0, c, 0, k⟩ [fm]⊢* ⟨a + k + 1, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show a + 1 = (a + 1) from rfl]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 2: R4 chain. From (k, 0, c, d, 0) drain a into d.
theorem phase2 : ∀ k : ℕ, ∀ c d,
    ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 3: R5/R1 alternation.
-- From (0, 0, k, d+2*k, e) to (0, 0, 0, d, e+2*k).
-- Each round: R5 then R1.
-- (0, 0, k+1, d+2*(k+1), e) = (0, 0, k+1, d+2*k+2, e)
-- R5: (0, 1, k+1, d+2*k+1, e+2)
-- R1: (0, 0, k, d+2*k, e+2)
theorem phase3 : ∀ k : ℕ, ∀ d e,
    ⟨0, 0, k, d + 2 * k, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 4: Final steps from (0, 0, 0, 2, 2*e) to (1, 0, 0, 0, 2*e+1).
-- (0, 0, 0, 2, 2*e) -> R5 -> (0, 1, 0, 1, 2*e+2)
-- -> R2 -> (1, 0, 0, 1, 2*e+2)
-- -> R3 -> (0, 2, 1, 1, 2*e+1)
-- -> R1 -> (0, 1, 0, 0, 2*e+1)
-- -> R2 -> (1, 0, 0, 0, 2*e+1)
theorem phase4 (e : ℕ) :
    ⟨0, 0, 0, 2, 2 * e⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2 * e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Main transition: (1, 0, 0, 0, e) ⊢⁺ (1, 0, 0, 0, 2*e+1)
-- Phase 1: (1, 0, 0, 0, e) ->* (e+1, 0, e, 0, 0) [using phase1 with a=0, c=0]
-- Phase 2: (e+1, 0, e, 0, 0) ->* (0, 0, e, 2*(e+1), 0) [using phase2 with k=e+1]
-- Phase 3: (0, 0, e, 2*(e+1), 0) = (0, 0, e, 2+2*e, 0) ->* (0, 0, 0, 2, 2*e)
-- Phase 4: (0, 0, 0, 2, 2*e) ⊢⁺ (1, 0, 0, 0, 2*e+1)
theorem main_trans (e : ℕ) :
    (1, 0, 0, 0, e) [fm]⊢⁺ (1, 0, 0, 0, 2 * e + 1) := by
  have h1 : (1, 0, 0, 0, e) [fm]⊢* (e + 1, 0, e, 0, 0) := by
    have := phase1 e 0 0; ring_nf at this ⊢; exact this
  have h2 : (e + 1, 0, e, 0, 0) [fm]⊢* (0, 0, e, 2 + 2 * e, 0) := by
    have := phase2 (e + 1) e 0; ring_nf at this ⊢; exact this
  have h3 : (0, 0, e, 2 + 2 * e, 0) [fm]⊢* (0, 0, 0, 2, 2 * e) := by
    have := phase3 e 2 0; ring_nf at this ⊢; exact this
  apply stepStar_stepPlus_stepPlus h1
  apply stepStar_stepPlus_stepPlus h2
  apply stepStar_stepPlus_stepPlus h3
  exact phase4 e

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨1, 0, 0, 0, e⟩) 0
  intro e; exact ⟨2 * e + 1, main_trans e⟩

end Sz22_2003_unofficial_5
