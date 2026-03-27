import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #397: [20/3, 33/35, 1/5, 49/2, 1/77, 5/7]

Vector representation:
```
 2 -1  1  0  0
 0  1 -1 -1  1
 0  0 -1  0  0
-1  0  0  2  0
 0  0  0 -1 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_397

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- Phase 2: (R2,R1) repeated k times
-- (a, 0, 1, d+k, e) →* (a+2k, 0, 1, d, e+k)
theorem r2r1_chain : ∀ k : ℕ, ∀ a d e,
    ⟨a, 0, 1, d+k, e⟩ [fm]⊢* ⟨a+2*k, (0 : ℕ), 1, d, e+k⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 2) d (e + 1))
    ring_nf; finish

-- Phase 4: R4 repeated k times
-- (a+k, 0, 0, d, e) →* (a, 0, 0, d+2k, e)
theorem r4_chain : ∀ k : ℕ, ∀ a d e,
    ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, (0 : ℕ), 0, d+2*k, e⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2) e)
    ring_nf; finish

-- Phase 5: R5 repeated k times
-- (0, 0, 0, d+k, e+k) →* (0, 0, 0, d, e)
theorem r5_chain : ∀ k : ℕ, ∀ d e,
    ⟨0, 0, 0, d+k, e+k⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro d e; exists 0
  | succ k ih =>
    intro d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    exact ih d e

-- Main transition: (0, 0, 0, d+2, 0) ⊢⁺ (0, 0, 0, 3*d+3, 0)
-- Phases:
-- 1. R6: (0,0,0,d+2,0) → (0,0,1,d+1,0)
-- 2. (R2,R1) x (d+1): (0,0,1,d+1,0) →* (2*(d+1),0,1,0,d+1)
-- 3. R3: (2*(d+1),0,1,0,d+1) → (2*(d+1),0,0,0,d+1)
-- 4. R4 x 2*(d+1): (2*(d+1),0,0,0,d+1) →* (0,0,0,4*(d+1),d+1)
-- 5. R5 x (d+1): (0,0,0,4*(d+1),d+1) →* (0,0,0,3*(d+1),0) = (0,0,0,3d+3,0)
theorem main_trans (d : ℕ) :
    ⟨0, 0, 0, d+2, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 3*d+3, 0⟩ := by
  -- Phase 1: R6
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, (d + 1) + 1, 0⟩ = some ⟨0, 0, 1, d + 1, 0⟩
    simp [fm]
  -- Phase 2: (R2,R1) chain
  apply stepStar_trans
  · have h := r2r1_chain (d+1) 0 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R3
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨2 * (d + 1), 0, 0 + 1, 0, d + 1⟩ = some ⟨2 * (d + 1), 0, 0, 0, d + 1⟩
    simp [fm]
  -- Phase 4: R4 chain
  apply stepStar_trans
  · have h := r4_chain (2*(d+1)) 0 0 (d+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 5: R5 chain
  have h := r5_chain (d+1) (3*(d+1)) 0
  convert h using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0 + 2, 0⟩)
  · execute fm 1
  · exact progress_nonhalt_simple (fm := fm)
      (fun n => ⟨0, 0, 0, n + 2, 0⟩) 0
      (fun n => ⟨3 * n + 1, main_trans n⟩)

end Sz22_2003_unofficial_397
