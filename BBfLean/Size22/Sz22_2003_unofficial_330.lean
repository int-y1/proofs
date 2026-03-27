import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #330: [18/35, 5/66, 14/3, 11/7, 9/2]

Vector representation:
```
 1  2 -1 -1  0
-1 -1  1  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_330

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a+1, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- Phase 1: (a, 0, 0, d, e) ⊢* (a, 0, 0, 0, d + e)
theorem r4_loop : ∀ d a e, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, 0, d + e⟩ := by
  intro d; induction' d with d ih <;> intro a e
  · simp; exists 0
  · step fm; apply stepStar_trans (ih a (e + 1)); ring_nf; finish

-- Phase 2: (a + 3*n + 1, 0, c, 0, 2*n) ⊢* (a + 1, 0, c + 2*n, 0, 0)
-- Each iteration does r5, r2, r2
theorem r522_loop : ∀ n a c, ⟨a + 3 * n + 1, 0, c, 0, 2 * n⟩ [fm]⊢* ⟨a + 1, 0, c + 2 * n, 0, 0⟩ := by
  intro n; induction' n with n ih <;> intro a c
  · simp; exists 0
  · rw [show a + 3 * (n + 1) + 1 = (a + 3 * n + 1) + 3 from by ring,
        show 2 * (n + 1) = 2 * n + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + 1 + 1 = c + 2 from by ring]
    apply stepStar_trans (ih a (c + 2))
    rw [show c + 2 + 2 * n = c + 2 * (n + 1) from by ring]
    finish

-- Phase 3 inner: r3, r1 pairs
theorem r31_loop : ∀ c a b, ⟨a, b + 1, c + 1, 0, 0⟩ [fm]⊢* ⟨a + 2 * (c + 1), b + c + 2, 0, 0, 0⟩ := by
  intro c; induction' c with c ih <;> intro a b
  · step fm; step fm; ring_nf; finish
  · step fm; step fm
    rw [show b + 1 + 1 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (b + 1))
    ring_nf; finish

-- Phase 3: r5 then r31_loop
theorem phase3 : ∀ n a, ⟨a + 1, 0, 2 * (n + 1), 0, 0⟩ [fm]⊢* ⟨a + 4 * (n + 1), 2 * (n + 1) + 2, 0, 0, 0⟩ := by
  intro n a
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (r31_loop (2 * n + 1) a 1)
  ring_nf; finish

-- Phase 4: (a, b, 0, d, 0) ⊢* (a + b, 0, 0, d + b, 0)
theorem r3_loop : ∀ b a d, ⟨a, b, 0, d, 0⟩ [fm]⊢* ⟨a + b, 0, 0, d + b, 0⟩ := by
  intro b; induction' b with b ih <;> intro a d
  · simp; exists 0
  · step fm; apply stepStar_trans (ih (a + 1) (d + 1)); ring_nf; finish

-- First step: rule 4 fires on (a, 0, 0, d+1, 0)
theorem first_step : ∀ a d, ⟨a, 0, 0, d + 1, 0⟩ [fm]⊢ ⟨a, 0, 0, d, 1⟩ := by
  intro a d; simp [fm]

-- Main transition
theorem main_trans : ∀ n a, a ≥ 3 * (n + 1) + 1 →
    ⟨a, 0, 0, 2 * (n + 1), 0⟩ [fm]⊢⁺ ⟨a + 3 * (n + 1) + 1, 0, 0, 2 * (n + 2), 0⟩ := by
  intro n a ha
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 3 * (n + 1) + 1 := ⟨a - 3 * (n + 1) - 1, by omega⟩
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (first_step _ _)
  -- After first step: (a' + 3*(n+1) + 1, 0, 0, 2*n+1, 1)
  -- Phase 1 continued: r4_loop
  apply stepStar_trans (r4_loop (2 * n + 1) (a' + 3 * (n + 1) + 1) 1)
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) from by ring]
  -- Phase 2: r522_loop
  apply stepStar_trans (r522_loop (n + 1) a' 0)
  rw [show 0 + 2 * (n + 1) = 2 * (n + 1) from by ring]
  -- Phase 3
  apply stepStar_trans (phase3 n a')
  -- Phase 4: r3_loop
  apply stepStar_trans (r3_loop (2 * (n + 1) + 2) (a' + 4 * (n + 1)) 0)
  rw [show 0 + (2 * (n + 1) + 2) = 2 * (n + 2) from by ring]
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 2, 0⟩) (by execute fm 14)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a n, q = ⟨a, 0, 0, 2 * (n + 1), 0⟩ ∧ a ≥ 3 * (n + 1) + 1)
  · intro q ⟨a, n, hq, ha⟩; subst hq
    exact ⟨_, ⟨a + 3 * (n + 1) + 1, n + 1, rfl, by omega⟩, main_trans n a ha⟩
  · exact ⟨5, 0, rfl, by omega⟩

end Sz22_2003_unofficial_330
