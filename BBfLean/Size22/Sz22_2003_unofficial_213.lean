import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #213: [1/6, 875/2, 2/55, 3/25, 242/7]

Vector representation:
```
-1 -1  0  0  0
-1  0  3  1  0
 1  0 -1  0 -1
 0  1 -2  0  0
 1  0  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_213

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- Phase A: R2/R3 alternation consuming e.
-- Each pair: (1, 0, c, d, e+1) → R2 → (0, 0, c+3, d+1, e+1) → R3 → (1, 0, c+2, d+1, e)
theorem r2r3_pairs : ∀ k c d, ⟨1, 0, c, d, k⟩ [fm]⊢* ⟨1, 0, c + 2 * k, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase A final R2: (1, 0, c, d, 0) → (0, 0, c+3, d+1, 0) when b=0
-- This is just one step of R2.

-- Phase B: R4 draining c pairs to b.
-- (0, b, 2*k+1, d, 0) →* (0, b+k, 1, d, 0) when a=0, e=0
theorem r4_drain : ∀ k, ∀ b d, ⟨0, b, 2 * k + 1, d, 0⟩ [fm]⊢* ⟨0, b + k, 1, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase C: 4-step transition from (0, n+2, 1, n+2, 0) to (0, n, 0, n+1, 1)
-- R5: (0, n+2, 1, n+2, 0) → (1, n+2, 1, n+1, 2)
-- R1: → (0, n+1, 1, n+1, 2)
-- R3: → (1, n+1, 0, n+1, 1)
-- R1: → (0, n, 0, n+1, 1)
theorem phase_c (n : ℕ) : ⟨0, n + 2, 1, n + 2, 0⟩ [fm]⊢* ⟨0, n, 0, n + 1, 1⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Phase D: R5/R1 drain.
-- Each pair: (0, b+1, 0, d+1, e) → R5 → (1, b+1, 0, d, e+2) → R1 → (0, b, 0, d, e+2)
theorem r5r1_drain : ∀ k d e, ⟨0, k, 0, d + k, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Main cycle: (1, 0, 0, 0, 2*k+1) ⊢⁺ (1, 0, 0, 0, 4*k+3)
theorem main_cycle (k : ℕ) : ⟨1, 0, 0, 0, 2 * k + 1⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 4 * k + 3⟩ := by
  -- Phase A: R2/R3 pairs consuming e=2k+1
  -- (1, 0, 0, 0, 2k+1) →* (1, 0, 2(2k+1), 2k+1, 0) = (1, 0, 4k+2, 2k+1, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 0, 4 * k + 2, 2 * k + 1, 0⟩)
  · have h := r2r3_pairs (2 * k + 1) 0 0
    simp only [Nat.zero_add] at h
    rw [show 2 * (2 * k + 1) = 4 * k + 2 from by ring] at h
    exact h
  -- Phase A final R2: (1, 0, 4k+2, 2k+1, 0) → (0, 0, 4k+5, 2k+2, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 4 * k + 5, 2 * k + 2, 0⟩)
  · step fm; finish
  -- Phase B: R4 drain c from 4k+5 down to 1, adding (2k+2) to b.
  -- (0, 0, 4k+5, 2k+2, 0) = (0, 0, 2*(2k+2)+1, 2k+2, 0) →* (0, 2k+2, 1, 2k+2, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2 * k + 2, 1, 2 * k + 2, 0⟩)
  · have h := r4_drain (2 * k + 2) 0 (2 * k + 2)
    simp only [Nat.zero_add] at h
    rw [show 2 * (2 * k + 2) + 1 = 4 * k + 5 from by ring] at h
    exact h
  -- Phase C: (0, 2k+2, 1, 2k+2, 0) →* (0, 2k, 0, 2k+1, 1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2 * k, 0, 2 * k + 1, 1⟩)
  · exact phase_c (2 * k)
  -- Phase D: R5/R1 drain b=2k, d going from 2k+1 to 1.
  -- (0, 2k, 0, 2k+1, 1) = (0, 2k, 0, 1 + 2k, 1) →* (0, 0, 0, 1, 1 + 2*(2k)) = (0, 0, 0, 1, 4k+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 1, 4 * k + 1⟩)
  · have h := r5r1_drain (2 * k) 1 1
    rw [show 1 + 2 * k = 2 * k + 1 from by ring,
        show 1 + 2 * (2 * k) = 4 * k + 1 from by ring] at h
    exact h
  -- Phase E: Final R5: (0, 0, 0, 1, 4k+1) → (1, 0, 0, 0, 4k+3)
  step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun k ↦ ⟨1, 0, 0, 0, 2 * k + 1⟩) 0
  intro k
  exact ⟨2 * k + 1, by
    show ⟨1, 0, 0, 0, 2 * k + 1⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2 * (2 * k + 1) + 1⟩
    rw [show 2 * (2 * k + 1) + 1 = 4 * k + 3 from by ring]
    exact main_cycle k⟩

end Sz22_2003_unofficial_213
