import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #101: [1/30, 4/77, 21/2, 5/7, 9317/3]

Vector representation:
```
-1 -1 -1  0  0
 2  0  0 -1 -1
-1  1  0  1  0
 0  0  1 -1  0
 0 -1  0  1  3
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_101

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e+3⟩
  | _ => none

-- R5,R2,R1,R1: one big loop iteration
theorem big_loop_one : ∀ b c e,
    ⟨0, b+3, c+2, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e+2⟩ := by
  intro b c e
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Iterate the big loop j times
theorem big_loop_iter : ∀ j, ∀ b c e,
    ⟨0, b+3*j, c+2*j, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e+2*j⟩ := by
  intro j; induction' j with j ih <;> intro b c e
  · exists 0
  rw [show b + 3 * (j + 1) = (b + 3 * j) + 3 from by ring,
      show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring]
  apply stepStar_trans (big_loop_one _ _ _)
  apply stepStar_trans (ih _ _ _)
  rw [show (e + 2) + 2 * j = e + 2 * (j + 1) from by ring]
  finish

-- R5,R2,R1: tail step when c=1
theorem tail_step : ∀ b e,
    ⟨0, b+2, 1, 0, e⟩ [fm]⊢* ⟨1, b, 0, 0, e+2⟩ := by
  intro b e
  step fm; step fm; step fm
  ring_nf; finish

-- Alternating R3,R2 chain: consume e, grow a and b
theorem r3r2_chain : ∀ j, ∀ a b e,
    ⟨a+1, b, 0, 0, e+j⟩ [fm]⊢* ⟨a+1+j, b+j, 0, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro a b e
  · exists 0
  rw [show e + (j + 1) = (e + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3 chain: transfer a to b and d
theorem a_to_bd : ∀ j, ∀ a b d,
    ⟨a+j, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+j, 0, d+j, 0⟩ := by
  intro j; induction' j with j ih <;> intro a b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 chain: transfer d to c
theorem d_to_c : ∀ j, ∀ b c d,
    ⟨0, b, c, d+j, 0⟩ [fm]⊢* ⟨0, b, c+j, d, 0⟩ := by
  intro j; induction' j with j ih <;> intro b c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Main transition: one full cycle of the canonical state
theorem main_trans (b k : ℕ) :
    ⟨0, b + 3*(k+2) + 2, 2*k+5, 0, 0⟩ [fm]⊢⁺ ⟨0, (b+k+2) + 3*(k+3) + 2, 2*(k+1)+5, 0, 0⟩ := by
  -- Phase 1: big_loop (k+2) iterations
  -- (0, b+3*(k+2)+2, 2*k+5, 0, 0) ->* (0, b+2, 1, 0, 2*(k+2))
  apply stepStar_stepPlus_stepPlus
  · have h := big_loop_iter (k+2) (b+2) 1 0
    simp only [(by ring : (b+2) + 3 * (k+2) = b + 3*(k+2) + 2),
               (by ring : 1 + 2 * (k+2) = 2*k+5),
               (by ring : 0 + 2 * (k+2) = 2*k+4)] at h
    exact h
  -- Phase 2: tail step
  -- (0, b+2, 1, 0, 2k+4) ->* (1, b, 0, 0, 2k+6)
  apply step_stepStar_stepPlus
  · show fm ⟨0, b + 2, 1, 0, 2 * k + 4⟩ = some ⟨0, b + 1, 1, 1, 2 * k + 7⟩; rfl
  apply stepStar_trans
  · show ⟨0, b + 1, 1, 1, 2 * k + 7⟩ [fm]⊢* ⟨2, b + 1, 1, 0, 2 * k + 6⟩
    step fm; finish
  apply stepStar_trans
  · show ⟨2, b + 1, 1, 0, 2 * k + 6⟩ [fm]⊢* ⟨1, b, 0, 0, 2 * k + 6⟩
    step fm; finish
  -- Phase 3: R3,R2 chain
  -- (1, b, 0, 0, 2k+6) ->* (2k+7, b+2k+6, 0, 0, 0)
  apply stepStar_trans
  · have h := r3r2_chain (2*k+6) 0 b 0
    simp only [(by ring : 0 + 1 = 1),
               (by ring : 0 + (2*k+6) = 2*k+6),
               (by ring : 0 + 1 + (2*k+6) = 2*k+7)] at h
    exact h
  -- Phase 4: R3 chain (a to b,d)
  -- (2k+7, b+2k+6, 0, 0, 0) ->* (0, b+4k+13, 0, 2k+7, 0)
  apply stepStar_trans
  · have h := a_to_bd (2*k+7) 0 (b+2*k+6) 0
    simp only [(by ring : (b+2*k+6) + (2*k+7) = b+4*k+13),
               (by ring : 0 + (2*k+7) = 2*k+7)] at h
    exact h
  -- Phase 5: R4 chain (d to c)
  -- (0, b+4k+13, 0, 2k+7, 0) ->* (0, b+4k+13, 2k+7, 0, 0)
  have h := d_to_c (2*k+7) (b+4*k+13) 0 0
  simp only [(by ring : 0 + (2*k+7) = 2*k+7)] at h
  rw [show (b+k+2) + 3*(k+3) + 2 = b+4*k+13 from by ring,
      show 2*(k+1)+5 = 2*k+7 from by ring]
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 8, 5, 0, 0⟩) (by execute fm 40)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨b, k⟩ ↦ ⟨0, b + 3*(k+2) + 2, 2*k+5, 0, 0⟩) ⟨0, 0⟩
  intro ⟨b, k⟩
  exact ⟨⟨b+k+2, k+1⟩, main_trans b k⟩

end Sz22_2003_unofficial_101
