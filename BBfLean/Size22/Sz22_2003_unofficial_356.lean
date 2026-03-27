import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #356: [2/15, 1617/2, 1/3, 25/7, 1/55, 3/5]

Vector representation:
```
 1 -1 -1  0  0
-1  1  0  2  1
 0 -1  0  0  0
 0  0  2 -1  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_356

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R2/R1 alternation: from (1,0,c+j,2j,j) consume c, building d and e
-- After j iterations: (1,0,c, 2j, j) with a=1
-- Each pair: R2 then R1
theorem r2r1_chain : ∀ j, ∀ c d e,
    ⟨1, 0, c + j, d, e⟩ [fm]⊢* ⟨1, 0, c, d + 2 * j, e + j⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  rw [show c + (j + 1) = (c + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 chain: transfer d to c (each d+1 -> c+2)
theorem d_to_c : ∀ j, ∀ c d e,
    ⟨0, 0, c, d + j, e⟩ [fm]⊢* ⟨0, 0, c + 2 * j, d, e⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  rw [show d + (j + 1) = (d + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5 chain: reduce c and e together
theorem r5_chain : ∀ j, ∀ c e,
    ⟨0, 0, c + j, 0, e + j⟩ [fm]⊢* ⟨0, 0, c, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro c e
  · exists 0
  rw [show c + (j + 1) = (c + j) + 1 from by ring,
      show e + (j + 1) = (e + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  finish

-- Main transition: (0, 1, c+1, 0, 0) ->+ (0, 1, 3*c+2, 0, 0)
theorem main_trans (c : ℕ) :
    ⟨0, 1, c + 1, 0, 0⟩ [fm]⊢⁺ ⟨0, 1, 3 * c + 2, 0, 0⟩ := by
  -- Phase 1: R1: (0,1,c+1,0,0) -> (1,0,c,0,0)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 1, c + 1, 0, 0⟩ = some ⟨1, 0, c, 0, 0⟩; rfl
  -- Phase 2: R2/R1 chain c times: (1,0,c,0,0) ->* (1,0,0,2c,c)
  apply stepStar_trans
  · have h := r2r1_chain c 0 0 0
    simp only [(by ring : 0 + 2 * c = 2 * c),
               (by ring : 0 + c = c)] at h
    exact h
  -- Phase 3: R2: (1,0,0,2c,c) -> (0,1,0,2c+2,c+1)
  step fm
  -- Phase 4: R3: (0,1,0,2c+2,c+1) -> (0,0,0,2c+2,c+1)
  step fm
  -- Phase 5: R4 chain: (0,0,0,2c+2,c+1) ->* (0,0,4c+4,0,c+1)
  apply stepStar_trans
  · have h := d_to_c (2 * c + 2) 0 0 (c + 1)
    simp only [(by ring : 0 + (2 * c + 2) = 2 * c + 2),
               (by ring : 0 + 2 * (2 * c + 2) = 4 * c + 4)] at h
    exact h
  -- Phase 6: R5 chain: (0,0,4c+4,0,c+1) ->* (0,0,3c+3,0,0)
  apply stepStar_trans
  · have h := r5_chain (c + 1) (3 * c + 3) 0
    simp only [(by ring : 3 * c + 3 + (c + 1) = 4 * c + 4),
               (by ring : 0 + (c + 1) = c + 1)] at h
    exact h
  -- Phase 7: R6: (0,0,3c+3,0,0) -> (0,1,3c+2,0,0)
  rw [show 3 * c + 3 = (3 * c + 2) + 1 from by ring]
  step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 2, 0, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 1, n + 1, 0, 0⟩) 1
  intro n
  exact ⟨3 * n + 1, main_trans n⟩

end Sz22_2003_unofficial_356
