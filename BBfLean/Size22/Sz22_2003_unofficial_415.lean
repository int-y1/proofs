import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #415: [25/63, 7/55, 2/5, 297/2, 7/3]

Vector representation:
```
 0 -2  2 -1  0
 0  0 -1  1 -1
 1  0 -1  0  0
-1  3  0  0  1
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_415

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer a to b and e
theorem r4_chain : ∀ j, ∀ a b e,
    ⟨a+j, b, 0, 0, e⟩ [fm]⊢* ⟨a, b+3*j, 0, 0, e+j⟩ := by
  intro j; induction' j with j ih <;> intro a b e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3 chain: transfer c to a
theorem r3_chain : ∀ j, ∀ a b c,
    ⟨a, b, c+j, 0, 0⟩ [fm]⊢* ⟨a+j, b, c, 0, 0⟩ := by
  intro j; induction' j with j ih <;> intro a b c
  · exists 0
  rw [show c + (j + 1) = (c + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5,R1 init: (0, b+3, 0, 0, e+1) ->* (0, b, 2, 0, e+1)
theorem r5r1_init : ∀ b e,
    ⟨0, b+3, 0, 0, e+1⟩ [fm]⊢* ⟨0, b, 2, 0, e+1⟩ := by
  intro b e
  step fm; step fm
  ring_nf; finish

-- One (R2,R1) pair: (0, b+2, c+1, 0, e+1) ->* (0, b, c+2, 0, e)
theorem r2r1_pair : ∀ b c e,
    ⟨0, b+2, c+1, 0, e+1⟩ [fm]⊢* ⟨0, b, c+2, 0, e⟩ := by
  intro b c e
  step fm; step fm
  ring_nf; finish

-- Iterate (R2,R1) j times
theorem r2r1_loop : ∀ j, ∀ b c e,
    ⟨0, b+2*j, c+1, 0, e+j⟩ [fm]⊢* ⟨0, b, c+1+j, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro b c e
  · exists 0
  rw [show b + 2 * (j + 1) = (b + 2 * j) + 2 from by ring,
      show e + (j + 1) = (e + j) + 1 from by ring]
  apply stepStar_trans (r2r1_pair _ _ _)
  rw [show c + 2 = (c + 1) + 1 from by ring]
  apply stepStar_trans (ih _ _ _)
  rw [show c + 1 + 1 + j = c + 1 + (j + 1) from by ring]
  finish

-- Main transition: C(k) ⊢⁺ C(k+1)
-- C(k) = (2k+5, k*(k+1), 0, 0, 0)
-- C(k+1) = (2k+7, (k+1)*(k+2), 0, 0, 0)
theorem main_trans (k : ℕ) :
    ⟨2*k+5, k*(k+1), 0, 0, 0⟩ [fm]⊢⁺ ⟨2*(k+1)+5, (k+1)*((k+1)+1), 0, 0, 0⟩ := by
  -- Phase 1: R4 chain (2k+5 times)
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (2*k+5) 0 (k*(k+1)) 0
    simp only [(by ring : 0 + (2*k+5) = 2*k+5),
               (by ring : k*(k+1) + 3 * (2*k+5) = k*k+7*k+15)] at h
    exact h
  -- Phase 2: R5,R1 init
  apply step_stepStar_stepPlus
  · show fm ⟨0, k*k+7*k+15, 0, 0, 2*k+5⟩ = some ⟨0, k*k+7*k+14, 0, 1, 2*k+5⟩; rfl
  apply stepStar_trans
  · show ⟨0, k*k+7*k+14, 0, 1, 2*k+5⟩ [fm]⊢* ⟨0, k*k+7*k+12, 2, 0, 2*k+5⟩
    step fm; finish
  -- Phase 3: R2,R1 loop (2k+5 times)
  apply stepStar_trans
  · have h := r2r1_loop (2*k+5) (k*k+3*k+2) 1 0
    simp only [(by ring : (k*k+3*k+2) + 2*(2*k+5) = k*k+7*k+12),
               (by ring : 0 + (2*k+5) = 2*k+5),
               (by ring : 1 + 1 + (2*k+5) = 2*k+7)] at h
    exact h
  -- Phase 4: R3 chain (2k+7 times)
  have h := r3_chain (2*k+7) 0 (k*k+3*k+2) 0
  simp only [(by ring : 0 + (2*k+7) = 2*k+7)] at h
  rw [show 2*(k+1)+5 = 2*k+7 from by ring,
      show (k+1)*((k+1)+1) = k*k+3*k+2 from by ring]
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2*0+5, 0*(0+1), 0, 0, 0⟩) (by execute fm 32)
  exact progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨2*k+5, k*(k+1), 0, 0, 0⟩) 0
    (fun k ↦ ⟨k+1, main_trans k⟩)

end Sz22_2003_unofficial_415
