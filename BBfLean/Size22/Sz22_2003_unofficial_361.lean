import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #361: [2/15, 3/14, 275/2, 49/55, 6/7]

Vector representation:
```
 1 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0 -1  2 -1
 1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_361

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R3 repeated: drain a, increasing c and e
theorem r3_chain : ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * a, 0, e + a⟩ := by
  have h : ∀ a c e, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * a, 0, e + a⟩ := by
    intro a; induction a with
    | zero => intro c e; exists 0
    | succ a ih =>
      intro c e
      rw [show c + 2 * (a + 1) = (c + 2) + 2 * a from by ring,
          show e + (a + 1) = (e + 1) + a from by ring]
      step fm
      exact ih _ _
  exact h a c e

-- R4 single step
theorem r4_step (c d k : ℕ) : (⟨0, 0, c + k + 1, d, k + 1⟩ : Q) [fm]⊢ ⟨0, 0, c + k, d + 2, k⟩ := by
  simp only [fm]

-- R4 repeated: convert c,e to d
theorem r4_chain : ⟨0, 0, c + k, d, k⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, 0⟩ := by
  have h : ∀ k c d, ⟨0, 0, c + k, d, k⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, 0⟩ := by
    intro k; induction k with
    | zero => intro c d; exists 0
    | succ k ih =>
      intro c d
      rw [show c + (k + 1) = c + k + 1 from by ring]
      apply stepStar_trans (step_stepStar (r4_step c d k))
      apply stepStar_trans (ih _ _)
      rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]
      finish
  exact h k c d

-- Climb step: R3, R1, R1
theorem climb_step : ⟨a + 1, b + 2, 0, 0, e⟩ [fm]⊢* ⟨a + 2, b, 0, 0, e + 1⟩ := by
  step fm; step fm; step fm; finish

-- Climb chain: k rounds of climb_step
theorem climb_chain : ⟨a + 1, b + 2 * k, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + k, b, 0, 0, e + k⟩ := by
  have h : ∀ k a b e, ⟨a + 1, b + 2 * k, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + k, b, 0, 0, e + k⟩ := by
    intro k; induction k with
    | zero => intro a b e; simp; exists 0
    | succ k ih =>
      intro a b e
      rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
      apply stepStar_trans climb_step
      rw [show a + 2 = (a + 1) + 1 from by ring]
      apply stepStar_trans (ih _ _ _)
      rw [show a + 1 + 1 + k = a + 1 + (k + 1) from by ring,
          show e + 1 + k = e + (k + 1) from by ring]
      finish
  exact h k a b e

-- R2, R5 pump step
theorem pump_step : ⟨1, b, 0, d + 2, 0⟩ [fm]⊢* ⟨1, b + 2, 0, d, 0⟩ := by
  step fm; step fm; finish

-- Pump chain: drain d into b
theorem pump_chain : ⟨1, b, 0, 2 * k, 0⟩ [fm]⊢* ⟨1, b + 2 * k, 0, 0, 0⟩ := by
  have h : ∀ k b, ⟨1, b, 0, 2 * k, 0⟩ [fm]⊢* ⟨1, b + 2 * k, 0, 0, 0⟩ := by
    intro k; induction k with
    | zero => intro b; simp; exists 0
    | succ k ih =>
      intro b
      rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
      apply stepStar_trans pump_step
      apply stepStar_trans (ih _)
      rw [show b + 2 + 2 * k = b + 2 * (k + 1) from by ring]
      finish
  exact h k b

-- Main cycle: (1, 2n+1, 0, 0, 0) ⊢⁺ (1, 4n+3, 0, 0, 0)
theorem cycle (n : ℕ) : ⟨1, 2 * n + 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨1, 4 * n + 3, 0, 0, 0⟩ := by
  -- Phase 1: climb n rounds: (1, 2n+1, 0, 0, 0) ⊢* (n+1, 1, 0, 0, n)
  rw [show 2 * n + 1 = 1 + 2 * n from by ring]
  apply stepStar_stepPlus_stepPlus (@climb_chain 0 1 n 0)
  rw [show 0 + 1 + n = n + 1 from by ring, show 0 + n = n from by ring]
  -- Phase 2: R3 then R1: (n+1, 1, 0, 0, n) ⊢ (n, 1, 2, 0, n+1) ⊢ (n+1, 0, 1, 0, n+1)
  apply step_stepStar_stepPlus (by unfold fm; rfl : (⟨n + 1, 1, 0, 0, n⟩ : Q) [fm]⊢ ⟨n, 1, 2, 0, n + 1⟩)
  step fm
  -- Phase 3: drain a via R3: (n+1, 0, 1, 0, n+1) ⊢* (0, 0, 2n+3, 0, 2n+2)
  apply stepStar_trans (@r3_chain (n + 1) 1 (n + 1))
  rw [show 1 + 2 * (n + 1) = 1 + (2 * n + 2) from by ring,
      show (n + 1) + (n + 1) = 2 * n + 2 from by ring]
  -- Phase 4: drain c,e via R4: (0, 0, 1+(2n+2), 0, 2n+2) ⊢* (0, 0, 1, 4n+4, 0)
  apply stepStar_trans (@r4_chain 1 (2 * n + 2) 0)
  rw [show 0 + 2 * (2 * n + 2) = 4 * n + 4 from by ring]
  -- Phase 5: kickstart: 3 fixed steps
  step fm; step fm; step fm
  -- Phase 6: pump chain: (1, 1, 0, 4n+2, 0) ⊢* (1, 4n+3, 0, 0, 0)
  rw [show 4 * n + 2 = 2 * (2 * n + 1) from by ring]
  apply stepStar_trans (@pump_chain 1 (2 * n + 1))
  rw [show 1 + 2 * (2 * n + 1) = 4 * n + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 1, 0, 0, 0⟩)
  · execute fm 5
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨1, 2 * n + 1, 0, 0, 0⟩)
  · intro c ⟨n, hq⟩; subst hq
    refine ⟨⟨1, 4 * n + 3, 0, 0, 0⟩, ⟨2 * n + 1, ?_⟩, cycle n⟩
    show (1, 4 * n + 3, 0, 0, 0) = (1, 2 * (2 * n + 1) + 1, 0, 0, 0)
    ring_nf
  · exact ⟨0, rfl⟩

end Sz22_2003_unofficial_361
