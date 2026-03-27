import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #548: [28/45, 33/2, 5/231, 15/11, 1/3]

Vector representation:
```
 2 -2 -1  1  0
-1  1  0  0  1
 0 -1  1 -1 -1
 0  1  1  0 -1
 0 -1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_548

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- Phase 1: R1,R2,R2 chain
theorem r1r2r2_chain : ∀ k c d e, ⟨0, 2, c+k, d, e⟩ [fm]⊢* ⟨0, 2, c, d+k, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2a: Two R3 steps
theorem r3r3_step : ⟨0, 2, 0, d+2, e+2⟩ [fm]⊢* ⟨0, 0, 2, d, e⟩ := by
  step fm; step fm; finish

-- Phase 2b: R4,R3 chain
theorem r4r3_chain : ∀ k c d e, ⟨0, 0, c, d+k, e+2*k⟩ [fm]⊢* ⟨0, 0, c+2*k, d, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2c: Two R4 steps to finish
theorem r4_two : ⟨0, 0, c, 0, 2⟩ [fm]⊢⁺ ⟨0, 2, c+2, 0, 0⟩ := by
  step fm; step fm; finish

-- Special case: (0, 2, 1, 0, 0) →⁺ (0, 2, 2, 0, 0)
theorem trans_base : ⟨0, 2, 1, 0, 0⟩ [fm]⊢⁺ ⟨0, 2, 2, 0, 0⟩ := by
  execute fm 5

-- Main transition for n≥1: (0, 2, n+2, 0, 0) →⁺ (0, 2, 2*n+4, 0, 0)
theorem trans_step : ⟨0, 2, n+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 2, 2*n+4, 0, 0⟩ := by
  -- Phase 1: (0,2,n+2,0,0) →* (0,2,0,n+2,2n+4)
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r1r2r2_chain (n+2) 0 0 0)
  simp only [Nat.zero_add]
  -- Phase 2a: (0,2,0,n+2,2n+4) →* (0,0,2,n,2n+2)
  rw [show n + 2 = n + 2 from rfl,
      show 2 * (n + 2) = 2 * n + 2 + 2 from by ring]
  apply stepStar_stepPlus_stepPlus r3r3_step
  -- Phase 2b: (0,0,2,n,2n+2) →* (0,0,2n+2,0,2)
  have h3 := r4r3_chain n 2 0 2
  simp only [Nat.zero_add] at h3
  rw [show 2 * n + 2 = 2 + 2 * n from by ring]
  apply stepStar_stepPlus_stepPlus h3
  -- Phase 2c: (0,0,2+2*n,0,2) →⁺ (0,2,2n+4,0,0)
  have h4 := r4_two (c := 2 + 2 * n)
  rw [show 2 + 2 * n + 2 = 2 * n + 4 from by ring] at h4
  exact h4

-- Combined main transition
theorem main_trans : ⟨0, 2, n+1, 0, 0⟩ [fm]⊢⁺ ⟨0, 2, 2*n+2, 0, 0⟩ := by
  rcases n with _ | n
  · exact trans_base
  · rw [show n + 1 + 1 = n + 2 from by ring,
        show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
    exact trans_step

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 1, 0, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2, n+1, 0, 0⟩) 0
  intro n; exists 2*n+1
  rw [show 2 * n + 1 + 1 = 2 * n + 2 from by ring]
  exact main_trans

end Sz22_2003_unofficial_548
