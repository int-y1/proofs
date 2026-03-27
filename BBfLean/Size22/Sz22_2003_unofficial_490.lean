import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #490: [28/15, 3/22, 25/2, 11/7, 154/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  1
 1  0 -1  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_490

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e+1⟩
  | _ => none

-- R4 repeated: convert d to e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 repeated: convert a to c
theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2+R1 interleaved chain
theorem r2r1_chain : ∀ k, ∀ a c d e, ⟨a+1, 0, c+k, d, e+k⟩ [fm]⊢* ⟨a+k+1, 0, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · simp; exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h (a+1) _ _ _)
  ring_nf; finish

-- Main transition: (0, 0, q+d+2, d, 0) ⊢⁺ (0, 0, q+2*d+4, d+2, 0)
theorem main_trans (q d : ℕ) :
    ⟨0, 0, q+d+2, d, 0⟩ [fm]⊢⁺ ⟨0, 0, q+2*d+4, d+2, 0⟩ := by
  -- Phase 1: R4 x d: (0,0,q+d+2,d,0) -> (0,0,q+d+2,0,d)
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_e d (q+d+2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5: (0,0,q+d+2,0,d) -> (1,0,q+d+1,1,d+1)
  rw [show q + d + 2 = (q + d + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, q+d+1, 1, d+1⟩)
  · show fm ⟨0, 0, (q+d+1)+1, 0, d⟩ = some ⟨1, 0, q+d+1, 1, d+1⟩; simp [fm]
  -- Phase 3: R2+R1 chain of (d+1) rounds
  -- Goal: (1, 0, q+d+1, 1, d+1) ⊢* (d+2, 0, q, d+2, 0)
  -- Use chain: (0+1, 0, q+(d+1), 1, 0+(d+1)) ⊢* (0+(d+1)+1, 0, q, 1+(d+1), 0)
  apply stepStar_trans (c₂ := ⟨d+2, 0, q, d+2, 0⟩)
  · rw [show d + 1 = 0 + (d + 1) from by ring]
    have h := r2r1_chain (d+1) 0 q 1 0
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase 4: R3 x (d+2): (d+2, 0, q, d+2, 0) -> (0, 0, q+2*(d+2), d+2, 0)
  have h := a_to_c (d+2) 0 q (d+2)
  simp only [Nat.zero_add] at h
  rw [show q + 2 * (d + 2) = q + 2 * d + 4 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨q, d⟩ ↦ ⟨0, 0, q+d+2, d, 0⟩) ⟨0, 0⟩
  intro ⟨q, d⟩; exists ⟨q+d, d+2⟩
  show ⟨0, 0, q+d+2, d, 0⟩ [fm]⊢⁺ ⟨0, 0, (q+d)+(d+2)+2, d+2, 0⟩
  rw [show (q+d)+(d+2)+2 = q+2*d+4 from by ring]
  exact main_trans q d

end Sz22_2003_unofficial_490
