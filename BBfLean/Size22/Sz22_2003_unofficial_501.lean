import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #501: [28/15, 3/22, 25/2, 121/7, 9/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  2
 0  2 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_501

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R4 repeated: convert d to e (when a=0, b=0)
theorem d_to_e : ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
  have many_step : ∀ k d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k d e

-- R3 repeated: convert a to c (when b=0, e=0)
theorem a_to_c : ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c+2*k, d, 0⟩ := by
  have many_step : ∀ k c, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c+2*k, d, 0⟩ := by
    intro k; induction' k with k h <;> intro c
    · exists 0
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k c

-- R2,R1 chain: interleaved pairs consuming c and e, building a and d
theorem r2r1_chain : ⟨a+1, 0, c+k+1, d, k+1⟩ [fm]⊢* ⟨a+k+2, 0, c, d+k+1, 0⟩ := by
  have many_step : ∀ k, ∀ a c d, ⟨a+1, 0, c+k+1, d, k+1⟩ [fm]⊢* ⟨a+k+2, 0, c, d+k+1, 0⟩ := by
    intro k; induction' k with k h <;> intro a c d
    · step fm; step fm; finish
    rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring]
    rw [show (k + 1) + 1 = (k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k a c d

-- Main transition: (0, 0, c+2d+5, d+1, 0) →⁺ (0, 0, c+4d+12, 2d+4, 0)
theorem main_trans : ⟨0, 0, c+2*d+5, d+1, 0⟩ [fm]⊢⁺ ⟨0, 0, c+4*d+12, 2*d+4, 0⟩ := by
  -- Phase 1: d_to_e
  rw [show d + 1 = 0 + (d + 1) from by ring]
  rw [show (0 : ℕ) = 0 + 2 * 0 from by ring]
  apply stepStar_stepPlus_stepPlus (@d_to_e (c+2*d+5) 0 (d+1) 0)
  -- Phase 2: R5 (gives us the ⊢⁺)
  rw [show c + 2 * d + 5 = (c + 2 * d + 4) + 1 from by ring]
  rw [show 0 + 2 * (d + 1) = (2 * d + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Now at (0, 2, c+2d+4, 0, 2d+1+1), need ⊢*
  -- Phase 3: R1, R1
  rw [show c + 2 * d + 4 = (c + 2 * d + 2) + 1 + 1 from by ring]
  step fm; step fm
  -- Now at (4, 0, c+2d+2, 2, 2d+1+1), need ⊢*
  -- Phase 4: r2r1_chain
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  rw [show c + 2 * d + 2 = c + (2 * d + 1) + 1 from by ring]
  apply stepStar_trans (@r2r1_chain 3 c (2*d+1) 2)
  -- Phase 5: a_to_c
  apply stepStar_trans (@a_to_c (3+(2*d+1)+2) c (2+(2*d+1)+1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 7, 2, 0⟩)
  · execute fm 8
  -- (0, 0, 7, 2, 0) = (0, 0, 0+2*1+5, 1+1, 0) with c=0, d=1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, d⟩ ↦ ⟨0, 0, c+2*d+5, d+1, 0⟩) ⟨0, 1⟩
  intro ⟨c, d⟩; exact ⟨⟨c+1, 2*d+3⟩, by
    show ⟨0, 0, c+2*d+5, d+1, 0⟩ [fm]⊢⁺ ⟨0, 0, (c+1)+2*(2*d+3)+5, (2*d+3)+1, 0⟩
    have h : (c+1)+2*(2*d+3)+5 = c+4*d+12 := by ring
    have h2 : (2*d+3)+1 = 2*d+4 := by ring
    rw [h, h2]
    exact main_trans⟩

end Sz22_2003_unofficial_501
