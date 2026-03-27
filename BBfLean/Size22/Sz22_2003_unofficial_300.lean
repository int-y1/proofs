import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #300: [15/2, 22/21, 1/3, 343/5, 1/77, 3/7]

Vector representation:
```
-1  1  1  0  0
 1 -1  0 -1  1
 0 -1  0  0  0
 0  0 -1  3  0
 0  0  0 -1 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_300

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R2/R1 zigzag: each iteration does R2 then R1
theorem zigzag_chain : ∀ k c d e,
    ⟨0, 1, c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), 1, c + k, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro c d e; simp; exists 0
  | succ k ih =>
    intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    show ⟨0, 0 + 1, c, (d + k) + 1, e⟩ [fm]⊢* _
    step fm
    step fm
    have h := ih (c + 1) d (e + 1)
    rw [show c + 1 + k = c + (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring] at h
    exact h

-- R4 chain: convert c to d
theorem r4_chain : ∀ k c d e,
    ⟨0, 0, c + k, d, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + 3 * k, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; simp; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    have h := ih c (d + 3) e
    rw [show d + 3 + 3 * k = d + 3 * (k + 1) from by ring] at h
    exact h

-- R5 chain: cancel d and e
theorem r5_chain : ∀ k d e,
    ⟨0, 0, 0, d + k, e + k⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro d e; simp; exists 0
  | succ k ih =>
    intro d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    exact ih d e

-- Main cycle using d = D + 2 to avoid subtraction:
-- (0,0,0,(D+2),0) →⁺ (0,0,0,2*D+2,0)
-- Phase 1: R6 step
-- Phase 2: zigzag D+1 pairs
-- Phase 3: R3 step
-- Phase 4: R4 chain D+1 steps
-- Phase 5: R5 chain D+1 steps
theorem main_cycle (D : ℕ) :
    ⟨0, 0, 0, D + 2, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 2 * D + 2, 0⟩ := by
  -- Phase 1: Rule 6: (0,0,0,D+2,0) → (0,1,0,D+1,0)
  show ⟨0, 0, 0, (D + 1) + 1, 0⟩ [fm]⊢⁺ _
  apply step_stepStar_stepPlus (by rfl : fm ⟨0, 0, 0, (D + 1) + 1, 0⟩ = some ⟨0, 1, 0, D + 1, 0⟩)
  -- Phase 2: zigzag (D+1) pairs: (0,1,0,D+1,0) →* (0,1,D+1,0,D+1)
  have h2 := zigzag_chain (D + 1) 0 0 0
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  -- Phase 3: Rule 3: (0,1,D+1,0,D+1) → (0,0,D+1,0,D+1)
  show ⟨0, 0 + 1, D + 1, 0, D + 1⟩ [fm]⊢* _
  step fm
  -- Phase 4: R4 chain: (0,0,D+1,0,D+1) →* (0,0,0,3*(D+1),D+1)
  have h4 := r4_chain (D + 1) 0 0 (D + 1)
  simp only [Nat.zero_add] at h4
  apply stepStar_trans h4
  -- Phase 5: R5 chain: (0,0,0,3*(D+1),D+1) →* (0,0,0,2*(D+1),0)
  -- 3*(D+1) = 2*(D+1) + (D+1)
  have h5 := r5_chain (D + 1) (2 * (D + 1)) 0
  simp only [Nat.zero_add] at h5
  rw [show 2 * (D + 1) + (D + 1) = 3 * (D + 1) from by ring] at h5
  apply stepStar_trans h5
  rw [show 2 * (D + 1) = 2 * D + 2 from by ring]
  finish

-- Bootstrap: c₀ →* (0,0,0,4,0)
theorem bootstrap : c₀ [fm]⊢* ⟨(0 : ℕ), 0, 0, 4, 0⟩ := by
  unfold c₀; execute fm 13

-- Cycle for parametric form
theorem cycle (n : ℕ) :
    ⟨0, 0, 0, 2 ^ n + 2, 0⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 2 ^ (n + 1) + 2, 0⟩ := by
  have h := main_cycle (2 ^ n)
  rw [show 2 * 2 ^ n + 2 = 2 ^ (n + 1) + 2 from by rw [pow_succ]; ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts bootstrap
  rw [show (4 : ℕ) = 2 ^ 1 + 2 from by norm_num]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 ^ (n + 1) + 2, 0⟩) 0
  intro n; exact ⟨n + 1, cycle (n + 1)⟩

end Sz22_2003_unofficial_300
