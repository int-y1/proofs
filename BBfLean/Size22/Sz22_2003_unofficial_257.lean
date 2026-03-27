import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #257: [14/15, 1/242, 39/2, 275/13, 2/77]

Vector representation:
```
 1 -1 -1  1  0  0
-1  0  0  0 -2  0
-1  1  0  0  0  1
 0  0  2  0  1 -1
 1  0  0 -1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_257

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+2, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+2, d, e+1, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- Phase A: R3,R1 pairs convert c→d,f: (1, 0, j, D, 0, F) →* (1, 0, 0, D+j, 0, F+j)
theorem r3r1_loop : ∀ j, ∀ D F,
    ⟨1, 0, j, D, 0, F⟩ [fm]⊢* ⟨1, 0, 0, D+j, 0, F+j⟩ := by
  intro j; induction' j with j ih <;> intro D F
  · exists 0
  rw [show (j + 1 : ℕ) = j + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase C: R4 loop converts f→c,e: (0, 0, C, D, E, j) →* (0, 0, C+2j, D, E+j, 0)
theorem r4_loop : ∀ j, ∀ C D E,
    ⟨0, 0, C, D, E, j⟩ [fm]⊢* ⟨0, 0, C+2*j, D, E+j, 0⟩ := by
  intro j; induction' j with j ih <;> intro C D E
  · exists 0
  rw [show (j + 1 : ℕ) = j + 1 from rfl]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase D: R5,R2 pairs drain e: (0, 0, C, D+j, E, 0) →* (0, 0, C, D, E-2j, 0)
-- where d≥j, e≥3j, after each (R5,R2) pair: d-=1, e-=3
-- Actually: (0, 0, C, D+j, 3j+r, 0) →* (0, 0, C, D, r, 0) with r<3 handled separately
-- More precisely: R5 gives (1, 0, C, D+j-1, 3j+r-1, 0), then R2 gives (0, 0, C, D+j-1, 3j+r-3, 0)

-- R5,R2 pair: (0, 0, C, D+1, E+3, 0) →* (0, 0, C, D, E, 0)
theorem r5r2_pair : ∀ j, ∀ C D,
    ⟨0, 0, C, D+j, 3*j+1, 0⟩ [fm]⊢* ⟨0, 0, C, D, 1, 0⟩ := by
  intro j; induction' j with j ih <;> intro C D
  · exists 0
  rw [show D + (j + 1) = (D + j) + 1 from by ring,
      show 3 * (j + 1) + 1 = (3 * j + 1) + 3 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  finish

-- Final R5 step: (0, 0, C, D+1, 1, 0) → (1, 0, C, D, 0, 0)
theorem final_r5 : ⟨0, 0, C, D+1, 1, 0⟩ [fm]⊢ ⟨1, 0, C, D, 0, 0⟩ := by
  show fm ⟨0, 0, C, D+1, 1, 0⟩ = some ⟨1, 0, C, D, 0, 0⟩; rfl

-- Phase B: 9 fixed steps from (1, 0, 0, 5k, 0, 3k) to (0, 0, 1, 5k+3, 0, 3k+1)
-- when k ≥ 1
theorem phase_b (k : ℕ) :
    ⟨1, 0, 0, 5*(k+1), 0, 3*(k+1)⟩ [fm]⊢⁺ ⟨0, 0, 1, 5*(k+1)+3, 0, 3*(k+1)+1⟩ := by
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  step fm
  ring_nf; finish

-- Main transition
theorem main_trans (k : ℕ) :
    ⟨1, 0, 3*(k+1), 2*(k+1), 0, 0⟩ [fm]⊢⁺ ⟨1, 0, 3*(2*(k+1)+1), 2*(2*(k+1)+1), 0, 0⟩ := by
  -- Phase A: (1, 0, 3(k+1), 2(k+1), 0, 0) →* (1, 0, 0, 5(k+1), 0, 3(k+1))
  apply stepStar_stepPlus_stepPlus
  · have h := r3r1_loop (3*(k+1)) (2*(k+1)) 0
    rw [show 2*(k+1) + 3*(k+1) = 5*(k+1) from by ring] at h
    simp only [Nat.zero_add] at h
    exact h
  -- Phase B: (1, 0, 0, 5(k+1), 0, 3(k+1)) →⁺ (0, 0, 1, 5(k+1)+3, 0, 3(k+1)+1)
  apply stepPlus_stepStar_stepPlus (phase_b k)
  -- Phase C: (0, 0, 1, 5(k+1)+3, 0, 3(k+1)+1) →* (0, 0, 6(k+1)+3, 5(k+1)+3, 3(k+1)+1, 0)
  apply stepStar_trans
  · have h := r4_loop (3*(k+1)+1) 1 (5*(k+1)+3) 0
    rw [show 1 + 2*(3*(k+1)+1) = 6*(k+1)+3 from by ring,
        show 0 + (3*(k+1)+1) = 3*(k+1)+1 from by ring] at h
    exact h
  -- Phase D: (0, 0, 6(k+1)+3, 5(k+1)+3, 3(k+1)+1, 0) →* (1, 0, 6(k+1)+3, 4(k+1)+2, 0, 0)
  apply stepStar_trans
  · have h := r5r2_pair (k+1) (6*(k+1)+3) (4*(k+1)+3)
    rw [show 4*(k+1)+3 + (k+1) = 5*(k+1)+3 from by ring] at h
    exact h
  -- Now at (0, 0, 6(k+1)+3, 4(k+1)+3, 1, 0)
  apply stepStar_trans
  · rw [show (4*(k+1)+3 : ℕ) = (4*(k+1)+2)+1 from by ring]
    exact step_stepStar final_r5
  -- (1, 0, 6(k+1)+3, 4(k+1)+2, 0, 0) = (1, 0, 3*(2*(k+1)+1), 2*(2*(k+1)+1), 0, 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 3, 2, 0, 0⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨1, 0, 3*(k+1), 2*(k+1), 0, 0⟩) 0
  intro k
  exact ⟨2*(k+1), by
    show ⟨1, 0, 3*(k+1), 2*(k+1), 0, 0⟩ [fm]⊢⁺ ⟨1, 0, 3*(2*(k+1)+1), 2*(2*(k+1)+1), 0, 0⟩
    exact main_trans k⟩

end Sz22_2003_unofficial_257
