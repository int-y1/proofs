import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #86: [5/6, 49/2, 484/35, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  2
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_86

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- Phase A: R4 repeated: e → b (when a=0, c=0)
-- (0, b, 0, d, e+k) →* (0, b+k, 0, d, e)
theorem e_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d, e+k⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show e + (k + 1) = e + k + 1 from by ring]
  step fm
  apply stepStar_trans (h (b + 1) d e)
  ring_nf; finish

-- Phase C: {R3, R1, R1} chain
-- (0, 2*k, c+1, d+k, e) →* (0, 0, c+k+1, d, e+2*k)
theorem r3r1r1_chain : ∀ k, ∀ c d e, ⟨0, 2*k, c+1, d+k, e⟩ [fm]⊢* ⟨0, 0, c+k+1, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  rw [show 2 * k + 1 + 1 = (2 * k + 1) + 1 from by ring]
  step fm
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (h (c + 1) d (e + 2))
  ring_nf; finish

-- Phase D: {R3, R2, R2} chain
-- From (0, 0, k, D+1, E) after k rounds: (0, 0, 0, D+3*k+1, E+2*k)
-- Each round from (0, 0, m+1, D'+1, E'):
--   R3: (2, 0, m, D', E'+2)
--   R2: (1, 0, m, D'+2, E'+2)
--   R2: (0, 0, m, D'+4, E'+2)
--   = (0, 0, m, (D'+3)+1, E'+2)
theorem r3r2r2_chain : ∀ k, ∀ D E, ⟨0, 0, k, D+1, E⟩ [fm]⊢* ⟨0, 0, 0, D+3*k+1, E+2*k⟩ := by
  intro k; induction' k with k h <;> intro D E
  · exists 0
  rw [show k + 1 = k + 1 from rfl]
  -- (0, 0, k+1, D+1, E) — c=k+1>=1, d=D+1>=1 → R3
  step fm
  step fm
  step fm
  -- Now at (0, 0, k, D+4, E+2) = (0, 0, k, (D+3)+1, E+2)
  apply stepStar_trans (h (D + 3) (E + 2))
  ring_nf; finish

-- Main transition: (0, 0, 0, 2*(d+1), 2*d) →⁺ (0, 0, 0, 2*(2*d+2), 2*(2*d+1))
theorem main_trans : ∀ d, ⟨0, 0, 0, 2*(d+1), 2*d⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*(2*d+2), 2*(2*d+1)⟩ := by
  intro d
  -- Phase A: R4 x 2d: (0,0,0,2*(d+1),2*d) → (0,2*d,0,2*(d+1),0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*d, 0, 2*(d+1), 0⟩)
  · have h := e_to_b (2*d) 0 (2*(d+1)) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase B: R5 x 1 step: (0, 2*d, 0, 2*(d+1), 0) → (0, 2*d, 1, 2*d+1, 0)
  -- 2*(d+1) = (2*d+1)+1, so R5 fires
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*d, 1, 2*d+1, 0⟩)
  · show fm ⟨0, 2*d, 0, (2*d+1)+1, 0⟩ = some ⟨0, 2*d, 1, 2*d+1, 0⟩
    simp [fm]
  -- Phase C: {R3, R1, R1} x d rounds: (0, 2*d, 1, 2*d+1, 0) → (0, 0, d+1, d+1, 2*d)
  -- r3r1r1_chain with k=d, c=0, d_param=d+1, e=0:
  -- LHS: (0, 2*d, 0+1, (d+1)+d, 0) = (0, 2*d, 1, 2*d+1, 0) ✓
  -- RHS: (0, 0, 0+d+1, d+1, 0+2*d) = (0, 0, d+1, d+1, 2*d) ✓
  apply stepStar_trans (c₂ := ⟨0, 0, d+1, d+1, 2*d⟩)
  · have h := r3r1r1_chain d 0 (d+1) 0
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase D: {R3, R2, R2} x (d+1) rounds: (0, 0, d+1, d+1, 2*d) → (0, 0, 0, 4*d+4, 4*d+2)
  -- r3r2r2_chain with k=d+1, D=d, E=2*d:
  -- LHS: (0, 0, d+1, d+1, 2*d) ✓
  -- RHS: (0, 0, 0, d+3*(d+1)+1, 2*d+2*(d+1)) = (0, 0, 0, 4*d+4, 4*d+2) ✓
  -- And 4*d+4 = 2*(2*d+2) ✓, 4*d+2 = 2*(2*d+1) ✓
  have h := r3r2r2_chain (d+1) d (2*d)
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨0, 0, 0, 2*(d+1), 2*d⟩) 0
  intro d; exact ⟨2*d+1, main_trans d⟩
