import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #468: [28/15, 21/22, 25/2, 11/7, 22/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  1 -1
-1  0  2  0  0
 0  0  0 -1  1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_468

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- Phase A: R3 repeated: convert a to c (b=0, e=0)
theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase B: R4 repeated: convert d to e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase D: (R2, R1) chain
theorem r2r1_chain : ∀ k a c d e, ⟨a+2, 0, c+k, d+2, e+k⟩ [fm]⊢* ⟨a+k+2, 0, c, d+2*k+2, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R2: (a+1, 1, (c+k)+1, d+3, e+k)
  rw [show (c + k) + 1 = (c + k + 1) from by ring]
  step fm  -- R1: (a+3, 0, c+k, d+4, e+k)
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Main transition: (2*n+2, 0, 0, 4*n+2, 0) ⊢⁺ (4*n+4, 0, 0, 8*n+6, 0)
theorem main_trans (n : ℕ) : ⟨2*n+2, 0, 0, 4*n+2, 0⟩ [fm]⊢⁺ ⟨4*n+4, 0, 0, 8*n+6, 0⟩ := by
  -- Phase A: R3 (2*n+2) times, then Phase B: R4 (4*n+2) times -> ⊢*
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans (c₂ := ⟨0, 0, 4*n+4, 4*n+2, 0⟩)
    · have h := a_to_c (2*n+2) 0 0 (4*n+2)
      simp only [Nat.zero_add, (by ring : 0 + 2 * (2 * n + 2) = 4 * n + 4)] at h
      exact h
    have h := d_to_e (4*n+2) (4*n+4) 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase C: R5, R2, R1 (3 explicit steps)
  step fm  -- R5: (1, 0, 4*n+3, 0, 4*n+3)
  step fm  -- R2: (0, 1, 4*n+3, 1, 4*n+2)
  rw [show 4 * n + 3 = (4 * n + 2) + 1 from by ring]
  step fm  -- R1: (2, 0, 4*n+2, 2, 4*n+2)
  -- Phase D: (R2, R1) chain (4*n+2) times
  apply stepStar_trans (c₂ := ⟨4*n+4, 0, 0, 8*n+6, 0⟩)
  · have h := r2r1_chain (4*n+2) 0 0 0 0
    simp only [Nat.zero_add, (by ring : 0 + (4 * n + 2) = 4 * n + 2)] at h
    convert h using 2; ring_nf
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨2*n+2, 0, 0, 4*n+2, 0⟩) 0
  intro n; exists 2*n+1
  show ⟨2*n+2, 0, 0, 4*n+2, 0⟩ [fm]⊢⁺ ⟨2*(2*n+1)+2, 0, 0, 4*(2*n+1)+2, 0⟩
  simp only [(by ring : 2 * (2 * n + 1) + 2 = 4 * n + 4),
             (by ring : 4 * (2 * n + 1) + 2 = 8 * n + 6)]
  exact main_trans n

end Sz22_2003_unofficial_468
