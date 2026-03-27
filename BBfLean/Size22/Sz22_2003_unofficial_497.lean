import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #497: [28/15, 3/22, 25/2, 121/7, 22/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  2
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_497

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R3 repeated: convert a to c (b=0, e=0)
theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 repeated: convert d to e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2+R1 chain: from (a+1, 0, c+k, d, e+k) to (a+k+1, 0, c, d+k, e)
theorem r2r1_chain : ∀ k a c d e, ⟨a+1, 0, c+k, d, e+k⟩ [fm]⊢* ⟨a+k+1, 0, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R2: (a, 1, (c+k)+1, d, e+k)
  rw [show (c + k) + 1 = (c + k + 1) from by ring]
  step fm  -- R1: (a+2, 0, c+k, d+1, e+k)
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Main transition: (d+1, 0, 0, d, 0) ⊢⁺ (2*d+2, 0, 0, 2*d+1, 0)
theorem main_trans (d : ℕ) : ⟨d+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2*d+2, 0, 0, 2*d+1, 0⟩ := by
  -- Phase 1+2 as ⊢*: R3 chain then R4 chain
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2*(d+1), 0, 2*d⟩)
  · apply stepStar_trans (c₂ := ⟨0, 0, 2*(d+1), d, 0⟩)
    · have h := a_to_c (d+1) 0 0 d
      simp only [Nat.zero_add] at h; exact h
    · have h := d_to_e d (2*(d+1)) 0 0
      simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 step (gives ⊢⁺) then R2/R1 chain (⊢*)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, 2*d+1, 0, 2*d+1⟩)
  · show fm ⟨0, 0, 2*(d+1), 0, 2*d⟩ = some ⟨1, 0, 2*d+1, 0, 2*d+1⟩
    simp only [fm, show 2 * (d + 1) = (2 * d + 1) + 1 from by ring]
  · have h := r2r1_chain (2*d+1) 0 0 0 0
    simp only [Nat.zero_add,
               (by ring : 0 + (2 * d + 1) = 2 * d + 1)] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨d+1, 0, 0, d, 0⟩) 1
  intro d; exists 2*d+1; exact main_trans d

end Sz22_2003_unofficial_497
