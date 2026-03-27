import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #343: [2/15, 1/14, 4719/2, 35/11, 4/91]

Vector representation:
```
 1 -1 -1  0  0  0
-1  0  0 -1  0  0
-1  1  0  0  2  1
 0  0  1  1 -1  0
 2  0  0 -1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_343

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+2, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | _ => none

-- Phase 1: Unwind b=2 from (0, 2, 0, 0, e+2, f)
-- 6 steps: R4, R1, R2, R4, R1, R2 → (0, 0, 0, 0, e, f)
theorem unwind_b2 : ⟨0, 2, 0, 0, e+2, f⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 0, e, f⟩ := by
  execute fm 6

-- Phase 2: R4 repeated: e to c,d
theorem e_to_cd : ∀ k c d, ⟨(0 : ℕ), 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c+k, d+k, 0, f⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    step fm
    apply stepStar_trans (ih (c+1) (d+1))
    ring_nf; finish

-- Phase 3: Descent from (0, 0, c, d+3, 0, f+1) consuming d by 3 and f by 1
-- Each round: R5, R2, R2
theorem descent_round : ⟨(0 : ℕ), 0, c, d+3, 0, f+1⟩ [fm]⊢⁺ ⟨0, 0, c, d, 0, f⟩ := by
  execute fm 3

theorem descent : ∀ k, ⟨(0 : ℕ), 0, c, d+3*k, 0, f+k⟩ [fm]⊢* ⟨0, 0, c, d, 0, f⟩ := by
  intro k; induction k with
  | zero => exists 0
  | succ k ih =>
    rw [show d + 3 * (k + 1) = (d + 3 * k) + 3 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    exact stepStar_trans (stepPlus_stepStar descent_round) ih

-- Phase 3b: Final descent step when d=1
-- R5: (0, 0, c, 1, 0, f+1) → (2, 0, c, 0, 0, f)
theorem descent_final : ⟨(0 : ℕ), 0, c, 1, 0, f+1⟩ [fm]⊢⁺ ⟨2, 0, c, 0, 0, f⟩ := by
  execute fm 1

-- Phase 4: Expansion from (2, 0, c+1, 0, e, f)
-- Each pair: R3, R1 → c decreases by 1, e increases by 2, f increases by 1
theorem expand_pair : ⟨2, 0, c+1, 0, e, f⟩ [fm]⊢⁺ ⟨2, 0, c, 0, e+2, f+1⟩ := by
  execute fm 2

theorem expand : ∀ k e f, ⟨2, 0, k, 0, e, f⟩ [fm]⊢* ⟨2, 0, 0, 0, e+2*k, f+k⟩ := by
  intro k; induction k with
  | zero => intro e f; simp; exists 0
  | succ k ih =>
    intro e f
    exact stepStar_trans (stepPlus_stepStar expand_pair) (by
      apply stepStar_trans (ih (e+2) (f+1))
      ring_nf; finish)

-- Phase 5: Final 2 steps from (2, 0, 0, 0, e, f) → (0, 2, 0, 0, e+4, f+2)
theorem final_expand : ⟨2, 0, 0, 0, e, f⟩ [fm]⊢⁺ ⟨(0 : ℕ), 2, 0, 0, e+4, f+2⟩ := by
  execute fm 2

-- Main cycle: (0, 2, 0, 0, 6*k, 4*k-1) ⊢⁺ (0, 2, 0, 0, 12*k, 8*k-1) for k ≥ 1
-- Using parameterization: (0, 2, 0, 0, 6*(k+1), 4*k+3)
-- Next state: (0, 2, 0, 0, 12*(k+1), 8*k+7) = (0, 2, 0, 0, 6*(2*k+2), 4*(2*k+1)+3)
theorem main_cycle (k : ℕ) :
    ⟨(0 : ℕ), 2, 0, 0, 6*(k+1), 4*k+3⟩ [fm]⊢⁺ ⟨0, 2, 0, 0, 12*(k+1), 8*k+7⟩ := by
  -- Phase 1: unwind b=2. Need 6*(k+1) = (6*(k+1)-2) + 2 = (6*k+4) + 2
  rw [show 6*(k+1) = (6*k+4) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus unwind_b2
  -- Now at (0, 0, 0, 0, 6*k+4, 4*k+3)
  -- Phase 2: e_to_cd. Convert all e to c,d
  rw [show (0 : ℕ) = 0 + 0 from by ring]
  apply stepStar_trans (e_to_cd (6*k+4) 0 0)
  simp only [Nat.zero_add]
  -- Now at (0, 0, 6*k+4, 6*k+4, 0, 4*k+3)
  -- Phase 3: descent. d = 6*k+4, we need d = 1 + 3*(2*k+1), f = (4*k+3) = (2*k+2) + (2*k+1)
  rw [show 6*k+4 = 1 + 3*(2*k+1) from by ring,
      show 4*k+3 = (2*k+2) + (2*k+1) from by ring]
  apply stepStar_trans (descent (2*k+1))
  -- Now at (0, 0, 6*k+4, 1, 0, 2*k+2)
  -- Phase 3b: descent_final
  rw [show 2*k+2 = (2*k+1) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar descent_final)
  -- Now at (2, 0, 6*k+4, 0, 0, 2*k+1)
  -- Phase 4: expand. c = 6*k+4
  rw [show 1 + 3 * (2 * k + 1) = 6*k+4 from by ring]
  apply stepStar_trans (expand (6*k+4) 0 (2*k+1))
  simp only [Nat.zero_add]
  -- Now at (2, 0, 0, 0, 2*(6*k+4), (2*k+1)+(6*k+4))
  -- = (2, 0, 0, 0, 12*k+8, 8*k+5)
  -- Phase 5: final_expand
  apply stepStar_trans (stepPlus_stepStar final_expand)
  -- Now at (0, 2, 0, 0, 12*k+8+4, 8*k+5+2) = (0, 2, 0, 0, 12*k+12, 8*k+7)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 6, 3⟩)
  · execute fm 10
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k, q = (⟨0, 2, 0, 0, 6*(k+1), 4*k+3⟩ : Q))
  · intro q ⟨k, hq⟩; subst hq
    refine ⟨⟨0, 2, 0, 0, 12*(k+1), 8*k+7⟩, ⟨2*k+1, ?_⟩, main_cycle k⟩
    ring_nf
  · exact ⟨0, by ring_nf⟩

end Sz22_2003_unofficial_343
