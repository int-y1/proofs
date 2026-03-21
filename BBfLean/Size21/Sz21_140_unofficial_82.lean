import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #82: [5/6, 44/35, 7/2, 3/11, 110/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  1  0
 0  1  0  0 -1
 1  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_82

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e+1⟩
  | _ => none

-- Phase 1: R3 repeated: a → d (when b=0, c=0)
-- (a+k, 0, 0, d, e) →* (a, 0, 0, d+k, e)
theorem a_to_d : ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+k, e⟩ := by
  have many_step : ∀ k a d, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+k, e⟩ := by
    intro k; induction' k with k h <;> intro a d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a d

-- Phase 2: R4 repeated: e → b (when a=0, c=0)
-- (0, b, 0, d, e+k) →* (0, b+k, 0, d, e)
theorem e_to_b : ⟨0, b, 0, d, e+k⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b e, ⟨0, b, 0, d, e+k⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b e

-- Middle phase: 3-step rounds
-- (1, 2*d, c, d, e) → (1, 2*(d-1), c+1, d-1, e+1) in 3 steps
-- Repeated d times: (1, 2*d, c, d, e) →* (1, 0, c+d, 0, e+d)
theorem middle_phase : ∀ k, ∀ c e, ⟨1, 2*k, c, k, e⟩ [fm]⊢* ⟨1, 0, c+k, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  -- State: (1, 2*(k+1), c, k+1, e)
  -- R1: a+1=1 (a=0), b+1=2k+2 (b=2k+1) → (0, 2k+1, c+1, k+1, e)
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
  step fm
  -- R2: c+1 >= 1, d+1 = k+1+1 → need c+1 >= 1 and k+1 >= 1
  rw [show k + 1 = k + 1 from rfl]
  step fm
  -- R1: a+1=2+1? No, a=2, b=2k+1. R1 needs a>=1 and b>=1
  rw [show 2 * k + 1 = 2 * k + 1 from rfl,
      show 2 = 1 + 1 from rfl]
  step fm
  -- Now at (1, 2*k, c+1, k, e+1)
  apply stepStar_trans (h (c+1) (e+1))
  ring_nf; finish

-- Tail phase: R3R2 alternating
-- Each pair: (a+1, 0, k+1, 0, e) →R3→ (a, 0, k+1, 1, e) →R2→ (a+2, 0, k, 0, e+1)
theorem tail_phase : ∀ k, ∀ a e, ⟨a+1, 0, k, 0, e⟩ [fm]⊢* ⟨a+1+k, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  -- (a+1, 0, k+1, 0, e)
  -- R3: (a, 0, k+1, 1, e)
  step fm
  -- R2: c=k+1>=1, d=1>=1: (a+2, 0, k, 0, e+1)
  step fm
  apply stepStar_trans (h (a+1) (e+1))
  ring_nf; finish

-- Main transition: (n+1, 0, 0, 0, 2*n) ⊢⁺ (n+2, 0, 0, 0, 2*(n+1))
theorem main_trans : ⟨n+1, 0, 0, 0, 2*n⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, 2*(n+1)⟩ := by
  -- Phase 1: R3 repeated (n+1) times: (n+1, 0, 0, 0, 2n) →* (0, 0, 0, n+1, 2n)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, n+1, 2*n⟩)
  · have h := @a_to_d 0 (n+1) 0 (2*n)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 repeated 2n times: (0, 0, 0, n+1, 2n) →* (0, 2n, 0, n+1, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*n, 0, n+1, 0⟩)
  · have h : ⟨0, 0, 0, n+1, 0 + 2*n⟩ [fm]⊢* ⟨0, 0 + 2*n, 0, n+1, 0⟩ := e_to_b
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 step: (0, 2n, 0, n+1, 0) → (1, 2n, 1, n, 1)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2*n, 1, n, 1⟩)
  · show fm ⟨0, 2*n, 0, n+1, 0⟩ = some ⟨1, 2*n, 1, n, 1⟩
    rw [show n + 1 = n + 1 from rfl]; simp [fm]
  -- Phase 4: Middle phase: (1, 2n, 1, n, 1) →* (1, 0, n+1, 0, n+1)
  apply stepStar_trans (c₂ := ⟨1, 0, n+1, 0, n+1⟩)
  · have h := @middle_phase n 1 1
    rw [show (1 : ℕ) + n = n + 1 from by omega] at h; exact h
  -- Phase 5: Tail phase: (1, 0, n+1, 0, n+1) →* (n+2, 0, 0, 0, 2n+2)
  have h := @tail_phase (n+1) 0 (n+1)
  rw [show 0 + 1 + (n + 1) = n + 2 from by ring,
      show n + 1 + (n + 1) = 2 * (n + 1) from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, 0, 2*n⟩)
    1
  intro n; exact ⟨n+1, main_trans⟩
