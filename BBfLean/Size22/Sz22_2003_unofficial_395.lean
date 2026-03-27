import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #395: [20/3, 27/175, 1/40, 147/2]

Vector representation:
```
 2 -1  1  0
 0  3 -2 -1
-3  0 -1  0
-1  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_395

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a, b, c+2, d+1⟩ => some ⟨a, b+3, c, d⟩
  | ⟨a+3, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+1, c, d+2⟩
  | _ => none

-- Phase 1: (1, 0, 0, d) →⁺ (3, 0, 2, d+4)
theorem phase1 : ∀ d, ⟨1, 0, 0, d⟩ [fm]⊢⁺ ⟨3, 0, 2, d+4⟩ := by
  intro d; execute fm 4

-- Phase 2: one climbing step via rule2 + 3x rule1
theorem climb_step : ∀ a c d, ⟨a, 0, c+2, d+1⟩ [fm]⊢* ⟨a+6, 0, c+3, d⟩ := by
  intro a c d; execute fm 4

-- Phase 2: full climb
theorem climb : ∀ D, ∀ a c, ⟨a, 0, c+2, D⟩ [fm]⊢* ⟨a+6*D, 0, c+2+D, 0⟩ := by
  intro D; induction D with
  | zero => intro a c; ring_nf; exists 0
  | succ D ih =>
    intro a c
    apply stepStar_trans (climb_step a c D)
    rw [show c + 3 = (c + 1) + 2 from by ring]
    apply stepStar_trans (ih (a + 6) (c + 1))
    ring_nf; exists 0

-- Phase 3: drain c using rule3
theorem drain_c : ∀ k, ∀ a, ⟨a+3*k, 0, k, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a; exists 0
  | succ k ih =>
    intro a
    rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring]
    step fm
    exact ih a

-- Phase 4: one drain step: rule4, rule1, rule3
theorem drain_a_step : ∀ a d, ⟨a+2+1, 0, 0, d⟩ [fm]⊢* ⟨a+1, 0, 0, d+2⟩ := by
  intro a d; execute fm 3

-- Phase 4: full drain of a
theorem drain_a : ∀ k, ∀ d, ⟨2*k+1, 0, 0, d⟩ [fm]⊢* ⟨1, 0, 0, d+2*k⟩ := by
  intro k; induction k with
  | zero => intro d; exists 0
  | succ k ih =>
    intro d
    rw [show 2 * (k + 1) + 1 = (2 * k) + 2 + 1 from by ring]
    apply stepStar_trans (drain_a_step (2 * k) d)
    apply stepStar_trans (ih (d + 2))
    ring_nf; exists 0

-- Main cycle for even d: (1, 0, 0, 2*n) ⊢⁺ (1, 0, 0, 6*n + 8)
theorem cycle : ∀ n, ⟨1, 0, 0, 2*n⟩ [fm]⊢⁺ ⟨1, 0, 0, 6*n+8⟩ := by
  intro n
  -- Phase 1: (1, 0, 0, 2*n) →⁺ (3, 0, 2, 2*n+4)
  apply stepPlus_stepStar_stepPlus (phase1 (2*n))
  -- Phase 2: (3, 0, 2, 2*n+4) →* (6*(2*n+4)+3, 0, 2*n+6, 0)
  have h2 := climb (2*n+4) 3 0
  rw [show (0 : ℕ) + 2 = 2 from by ring] at h2
  apply stepStar_trans h2
  -- Phase 3: drain c
  rw [show 3 + 6 * (2 * n + 4) = (6 * n + 9) + 3 * (2 * n + 6) from by ring,
      show 2 + (2 * n + 4) = 2 * n + 6 from by ring]
  apply stepStar_trans (drain_c (2*n+6) (6*n+9))
  -- Phase 4: drain a
  rw [show 6 * n + 9 = 2 * (3 * n + 4) + 1 from by ring]
  apply stepStar_trans (drain_a (3*n+4) 0)
  ring_nf; exists 0

-- Recurrence: dseq(0) = 0, dseq(i+1) = 3*dseq(i) + 4
def dseq : ℕ → ℕ
  | 0 => 0
  | i+1 => 3 * dseq i + 4

theorem dseq_step : ∀ i, 2 * dseq (i + 1) = 6 * dseq i + 8 := by
  intro i; simp [dseq]; ring

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0⟩)
  · exists 0
  apply progress_nonhalt_simple (fm := fm) (fun i ↦ ⟨1, 0, 0, 2 * dseq i⟩) 0
  intro i
  exact ⟨i + 1, by rw [dseq_step]; exact cycle (dseq i)⟩

end Sz22_2003_unofficial_395
