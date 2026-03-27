import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #110: [1/30, 6/77, 49/2, 25/7, 242/5]

Vector representation:
```
-1 -1 -1  0  0
 1  1  0 -1 -1
-1  0  0  2  0
 0  0  2 -1  0
 1  0 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_110

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- Phase 1: transfer a to d (rule 3), accumulating in d
-- (a, b, 0, d, 0) →* (0, b, 0, d+2*a, 0)
theorem phase1 : ∀ a, ∀ b d, ⟨a, b, 0, d, 0⟩ [fm]⊢* ⟨0, b, 0, d+2*a, 0⟩ := by
  intro a; induction' a with a ih <;> intro b d
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 2: transfer d to c (rule 4), accumulating in c
-- (0, b, c, d, 0) →* (0, b, c+2*d, 0, 0)
theorem phase2 : ∀ d, ∀ b c, ⟨0, b, c, d, 0⟩ [fm]⊢* ⟨0, b, c+2*d, 0, 0⟩ := by
  intro d; induction' d with d ih <;> intro b c
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 3: interleaved rule5+rule1, draining b
-- (0, b, (c+2)+2*b, 0, e) →* (0, 0, c+2, 0, e+2*b)
theorem phase3 : ∀ b, ∀ c e, ⟨0, b, (c+2)+2*b, 0, e⟩ [fm]⊢* ⟨0, 0, c+2, 0, e+2*b⟩ := by
  intro b; induction' b with b ih <;> intro c e
  · simp; exists 0
  rw [show (c + 2) + 2 * (b + 1) = ((c + 2) + 2 * b) + 1 + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 4: 10 fixed steps
-- (0, 0, 4, 0, e) →* (2, 2, 0, 0, e)
theorem phase4 : ∀ e, ⟨0, 0, 4, 0, e⟩ [fm]⊢* ⟨2, 2, 0, 0, e⟩ := by
  intro e
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm
  finish

-- Phase 5: transfer e to a,b (3 steps per round)
-- (a+2, 2*a+2, 0, 0, 2*k) →* (a+k+2, 2*a+2*k+2, 0, 0, 0)
theorem phase5 : ∀ k, ∀ a, ⟨a+2, 2*a+2, 0, 0, 2*k⟩ [fm]⊢* ⟨a+k+2, 2*a+2*k+2, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show a + 1 + 2 = (a + 1) + 2 from by ring]
  rw [show 2 * a + 2 + 1 + 1 = 2 * (a + 1) + 2 from by ring]
  apply stepStar_trans (ih _)
  ring_nf; finish

-- All phases combined as stepStar
theorem all_phases : ∀ n, ⟨n+1, 2*n, 0, 0, 0⟩ [fm]⊢* ⟨2*n+2, 2*(2*n+1), 0, 0, 0⟩ := by
  intro n
  -- Phase 1: (n+1, 2n, 0, 0, 0) →* (0, 2n, 0, 2(n+1), 0)
  apply stepStar_trans (phase1 (n+1) (2*n) 0)
  rw [show 0 + 2 * (n + 1) = 2 * (n + 1) from by ring]
  -- Phase 2: →* (0, 2n, 4(n+1), 0, 0)
  apply stepStar_trans (phase2 (2*(n+1)) (2*n) 0)
  rw [show 0 + 2 * (2 * (n + 1)) = (2 + 2) + 2 * (2 * n) from by ring]
  -- Phase 3: →* (0, 0, 4, 0, 4n)
  apply stepStar_trans (phase3 (2*n) 2 0)
  rw [show 0 + 2 * (2 * n) = 4 * n from by ring]
  -- Phase 4: →* (2, 2, 0, 0, 4n)
  apply stepStar_trans (phase4 (4*n))
  -- Phase 5: →* (2n+2, 4n+2, 0, 0, 0)
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  rw [show (2 : ℕ) = 2 * 0 + 2 from by ring]
  rw [show 4 * n = 2 * (2 * n) from by ring]
  apply stepStar_trans (phase5 (2*n) 0)
  ring_nf; finish

-- Main transition as stepPlus (needed for nonhalt)
theorem main_trans : ∀ n, ⟨n+1, 2*n, 0, 0, 0⟩ [fm]⊢⁺ ⟨2*n+2, 2*(2*n+1), 0, 0, 0⟩ := by
  intro n
  apply stepStar_stepPlus (all_phases n)
  simp [Q]
  omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 2, 0, 0, 0⟩)
  · execute fm 13
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (C := fun n ↦ ⟨n+1, 2*n, 0, 0, 0⟩) (i₀ := 1)
  intro n
  exact ⟨2*n+1, main_trans n⟩

end Sz22_2003_unofficial_110
