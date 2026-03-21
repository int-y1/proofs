import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #22: [28/15, 3/22, 25/2, 121/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  2
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_22

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1: R3 repeated: a → c (when b=0, e=0)
-- (a+k, 0, c, d, 0) →* (a, 0, c+2*k, d, 0)
theorem a_to_c : ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  have many_step : ∀ k a c, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
    intro k; induction' k with k h <;> intro a c
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a c

-- Phase 2: R4 repeated: d → e (when a=0, b=0)
-- (0, 0, c, d+k, e) →* (0, 0, c, d, e+2*k)
theorem d_to_e : ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
  have many_step : ∀ k d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k d e

-- Phase 3: Interleaved R1/R2 chain
-- (a, 1, c+k, d, k) →* (a+k, 1, c, d+k, 0)
theorem r1r2_chain : ∀ k, ∀ a d, ⟨a, 1, c+k, d, k⟩ [fm]⊢* ⟨a+k, 1, c, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Full phase 3: (0, 0, E+2, 0, E) →* (E+2, 0, 0, E+1, 0) for E ≥ 0
theorem phase3 (E : ℕ) : ⟨0, 0, E+2, 0, E⟩ [fm]⊢* ⟨E+2, 0, 0, E+1, 0⟩ := by
  -- R5: (0, 0, (E+1)+1, 0, E) → (0, 1, E+1, 0, E)
  rw [show E + 2 = (E + 1) + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨0, 1, E+1, 0, E⟩)
  · step fm; finish
  -- r1r2_chain with c=1: (0, 1, 1+E, 0, E) →* (E, 1, 1, E, 0)
  apply stepStar_trans (c₂ := ⟨E, 1, 1, E, 0⟩)
  · have h := @r1r2_chain 1 E 0 0
    rw [show 1 + E = E + 1 from by ring] at h
    simp only [Nat.zero_add] at h
    exact h
  -- Final R1: (E, 1, 1, E, 0) → (E+2, 0, 0, E+1, 0)
  step fm
  finish

-- Main transition: (d+1, 0, 0, d, 0) ⊢⁺ (2d+2, 0, 0, 2d+1, 0)
theorem main_trans : ⟨d+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2*d+2, 0, 0, 2*d+1, 0⟩ := by
  -- First R3 step (gives stepPlus): (d+1, 0, 0, d, 0) → (d, 0, 2, d, 0)
  apply step_stepStar_stepPlus (c₂ := ⟨d, 0, 2, d, 0⟩)
  · show fm ⟨d + 1, 0, 0, d, 0⟩ = some ⟨d, 0, 2, d, 0⟩
    simp [fm]
  -- R3 x d: (d, 0, 2, d, 0) →* (0, 0, 2d+2, d, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, 2+2*d, d, 0⟩)
  · have h := @a_to_c 0 d 2 d
    simp only [Nat.zero_add] at h; exact h
  -- R4 x d: (0, 0, 2d+2, d, 0) →* (0, 0, 2d+2, 0, 2d)
  apply stepStar_trans (c₂ := ⟨0, 0, 2+2*d, 0, 2*d⟩)
  · have h := @d_to_e (2+2*d) 0 d 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: (0, 0, 2d+2, 0, 2d) →* (2d+2, 0, 0, 2d+1, 0)
  have h := phase3 (2*d)
  rw [show 2 * d + 2 = 2 + 2 * d from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨d+1, 0, 0, d, 0⟩) 0
  intro d; exact ⟨2*d+1, main_trans⟩

end Sz21_140_unofficial_22
