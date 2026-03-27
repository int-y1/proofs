import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #489: [28/15, 3/22, 25/2, 11/7, 147/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_489

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- Phase 1: R4 chain, d → e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase 5: R3 chain, a → c (each step adds 2 to c)
theorem a_to_c : ∀ k a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, (0 : ℕ), c + 2 * k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase 3: R1-R2 interleaved chain
-- From state (a, 1, c+j, d, j): j rounds of (R1, R2)
-- Each R1: (a, 0+1, c'+1, d, e) → (a+2, 0, c', d+1, e)
-- Each R2: (a'+1, 0, c', d, e'+1) → (a', 0+1, c', d, e')
-- Net per round: a += 1, c -= 1, d += 1, e -= 1
theorem r1r2_chain : ∀ j a c d, ⟨a, 1, c + j, d, j⟩ [fm]⊢* ⟨a + j, (1 : ℕ), c, d + j, 0⟩ := by
  intro j; induction j with
  | zero => intro a c d; exists 0
  | succ j ih =>
    intro a c d
    rw [show c + (j + 1) = (c + j) + 1 from by ring,
        show (j : ℕ) + 1 = j + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring,
        show (j : ℕ) + 1 = j + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c _)
    ring_nf; finish

-- Main transition: (0, 0, c+d+9, d+6, 0) ⊢⁺ (0, 0, c+2*d+17, d+9, 0)
-- Phases:
-- 1. R4 × (d+6): (0,0,c+d+9,d+6,0) → (0,0,c+d+9,0,d+6)
-- 2. R5: (0,0,c+d+9,0,d+6) → (0,1,c+d+8,2,d+6)
-- 3. (R1,R2) × (d+6): (0,1,c+d+8,2,d+6) → (d+6,1,c+2,d+8,0)
-- 4. R1: (d+6,1,c+2,d+8,0) → (d+8,0,c+1,d+9,0)
-- 5. R3 × (d+8): (d+8,0,c+1,d+9,0) → (0,0,c+2d+17,d+9,0)
theorem main_trans (c d : ℕ) : ⟨0, 0, c + d + 9, d + 6, 0⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * d + 17, d + 9, 0⟩ := by
  -- Phase 1: R4 × (d+6)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, c + d + 9, 0, d + 6⟩)
  · have h := d_to_e (d + 6) (c + d + 9) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, c + d + 8, 2, d + 6⟩)
  · rw [show c + d + 9 = (c + d + 8) + 1 from by ring]
    simp [fm]
  -- Phase 3: (R1,R2) × (d+6)
  apply stepStar_trans (c₂ := ⟨d + 6, 1, c + 2, d + 6 + 2, 0⟩)
  · rw [show c + d + 8 = (c + 2) + (d + 6) from by ring]
    have h := r1r2_chain (d + 6) 0 (c + 2) 2
    simp only [Nat.zero_add] at h
    rw [show (2 : ℕ) + (d + 6) = d + 8 from by ring] at h
    rw [show d + 6 + 2 = d + 8 from by ring]
    exact h
  -- Phase 4: R1 (one step)
  apply stepStar_trans (c₂ := ⟨d + 8, 0, c + 1, d + 9, 0⟩)
  · rw [show d + 8 = d + 6 + 2 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring,
        show c + 2 = (c + 1) + 1 from by ring]
    step fm; ring_nf; finish
  -- Phase 5: R3 × (d+8)
  · have h := a_to_c (d + 8) 0 (c + 1) (d + 9)
    simp only [Nat.zero_add] at h
    rw [show c + 1 + 2 * (d + 8) = c + 2 * d + 17 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 9, 6, 0⟩) (by execute fm 21)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, d⟩ ↦ ⟨0, 0, c + d + 9, d + 6, 0⟩) ⟨0, 0⟩
  intro ⟨c, d⟩
  refine ⟨⟨c + d + 5, d + 3⟩, ?_⟩
  show ⟨0, 0, c + d + 9, d + 6, 0⟩ [fm]⊢⁺ ⟨0, 0, (c + d + 5) + (d + 3) + 9, (d + 3) + 6, 0⟩
  rw [show (c + d + 5) + (d + 3) + 9 = c + 2 * d + 17 from by ring,
      show (d + 3) + 6 = d + 9 from by ring]
  exact main_trans c d

end Sz22_2003_unofficial_489
