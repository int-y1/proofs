import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #262: [14/15, 1/3, 3993/2, 5/11, 1/35, 3/5]

Vector representation:
```
 1 -1 -1  1  0
 0 -1  0  0  0
-1  1  0  0  3
 0  0  1  0 -1
 0  0 -1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_262

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+3⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1: R6/R1/R3 loop. (0,1,j,D,E) →* (0,1,0,D+j,E+3*j)
-- Each iteration: R1 then R3.
-- R1: (0,1,j+1,D,E) → (1,0,j,D+1,E) then R3: → (0,1,j,D+1,E+3)
theorem r1r3_loop : ∀ j D E, ⟨0, 1, j, D, E⟩ [fm]⊢* ⟨0, 1, 0, D+j, E+3*j⟩ := by
  intro j; induction' j with j ih <;> intro D E
  · exists 0
  rw [show (j + 1 : ℕ) = j + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 2: R4 loop. (0,0,C,D,j) →* (0,0,C+j,D,0)
theorem r4_loop : ∀ j C D, ⟨0, 0, C, D, j⟩ [fm]⊢* ⟨0, 0, C+j, D, 0⟩ := by
  intro j; induction' j with j ih <;> intro C D
  · exists 0
  rw [show (j + 1 : ℕ) = j + 1 from rfl]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 3: R5 loop. (0,0,C+j,j,0) →* (0,0,C,0,0)
theorem r5_loop : ∀ j C, ⟨0, 0, C+j, j, 0⟩ [fm]⊢* ⟨0, 0, C, 0, 0⟩ := by
  intro j; induction' j with j ih <;> intro C
  · exists 0
  rw [show C + (j + 1) = (C + j) + 1 from by ring]
  step fm
  exact ih C

-- Main transition: (0,0,n+1,0,0) ⊢* (0,0,2*n,0,0) for n >= 1
-- From (0,0,n+1,0,0):
--   R6: (0,1,n,0,0)
--   r1r3_loop n times: (0,1,0,n,3*n)
--   R2: (0,0,0,n,3*n)
--   r4_loop: (0,0,3*n,n,0)
--   r5_loop: (0,0,2*n,0,0)
theorem main_trans_star (n : ℕ) :
    ⟨0, 0, n+1, 0, 0⟩ [fm]⊢* ⟨0, 0, 2*n, 0, 0⟩ := by
  -- R6: (0,0,n+1,0,0) → (0,1,n,0,0)
  step fm
  -- r1r3_loop
  apply stepStar_trans (r1r3_loop n 0 0)
  rw [show (0 : ℕ) + n = n from by ring, show (0 : ℕ) + 3 * n = 3 * n from by ring]
  -- R2: (0,1,0,n,3*n) → (0,0,0,n,3*n)
  step fm
  -- r4_loop
  apply stepStar_trans (r4_loop (3*n) 0 n)
  rw [show (0 : ℕ) + 3 * n = 3 * n from by ring]
  -- r5_loop
  rw [show (3 * n : ℕ) = 2 * n + n from by ring]
  exact r5_loop n (2*n)

theorem main_trans (n : ℕ) :
    ⟨0, 0, n+3, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*n+4, 0, 0⟩ := by
  rw [show n + 3 = (n + 2) + 1 from by ring, show 2 * n + 4 = 2 * (n + 2) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (n + 2) + 1, 0, 0⟩ = some ⟨0, 1, n + 2, 0, 0⟩; rfl
  apply stepStar_trans (r1r3_loop (n+2) 0 0)
  rw [show (0 : ℕ) + (n + 2) = n + 2 from by ring,
      show (0 : ℕ) + 3 * (n + 2) = 3 * (n + 2) from by ring]
  step fm
  apply stepStar_trans (r4_loop (3*(n+2)) 0 (n+2))
  rw [show (0 : ℕ) + 3 * (n + 2) = 3 * (n + 2) from by ring,
      show 3 * (n + 2) = 2 * (n + 2) + (n + 2) from by ring]
  exact r5_loop (n+2) (2*(n+2))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun k ↦ ⟨0, 0, k+3, 0, 0⟩) 0
  intro k
  exact ⟨2*k+1, by
    show ⟨0, 0, k+3, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, (2*k+1)+3, 0, 0⟩
    rw [show (2 * k + 1) + 3 = 2 * k + 4 from by ring]
    exact main_trans k⟩

end Sz22_2003_unofficial_262
