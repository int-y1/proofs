import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #612: [35/6, 121/2, 4/55, 9/7, 35/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  2  0 -1  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_612

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · simp; exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R1,R1,R3 interleaved chain
theorem r1r1r3_chain : ∀ k, ∀ c d e, ⟨2, 2*k, c, d, k+e⟩ [fm]⊢* ⟨2, 0, c+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · simp; exists 0
  rw [show 2 * (k + 1) = (2 * k) + 2 from by ring,
      show (k + 1) + e = k + (e + 1) from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2,R2,R3 drain chain
theorem r2r2r3_chain : ∀ k, ∀ c e, ⟨2, 0, c+k, d, e⟩ [fm]⊢* ⟨2, 0, c, d, e+3*k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · simp; exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Main transition: (0, 0, 0, D+1, 2*D+4) ->+ (0, 0, 0, 2*D+3, 4*D+8)
theorem main_trans (n : ℕ) : ⟨0, 0, 0, n+1, 2*n+4⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*n+3, 4*n+8⟩ := by
  -- Phase 1: R4 chain
  rw [show (n : ℕ) + 1 = 0 + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (n+1) 0)
  rw [show 0 + 2 * (n + 1) = 2 * n + 2 from by ring]
  -- Phase 2: R5+R3 opening
  rw [show 2 * n + 4 = (2 * n + 2) + 1 + 1 from by ring]
  step fm; step fm
  -- Phase 3: R1,R1,R3 chain
  have h3 := r1r1r3_chain (n+1) 0 1 (n+1)
  rw [show (n + 1) + (n + 1) = 2 * n + 2 from by ring,
      show 2 * (n + 1) = 2 * n + 2 from by ring,
      show 0 + (n + 1) = n + 1 from by ring,
      show 1 + (2 * n + 2) = 2 * n + 3 from by ring] at h3
  apply stepStar_trans h3
  -- Phase 4: R2,R2,R3 chain
  have h4 := @r2r2r3_chain (2*n+3) (n+1) 0 (n+1)
  rw [show 0 + (n + 1) = n + 1 from by ring,
      show (n + 1) + 3 * (n + 1) = 4 * n + 4 from by ring] at h4
  apply stepStar_trans h4
  -- Phase 5: Final R2,R2
  step fm; step fm
  rw [show 4 * n + 4 + 2 + 2 = 4 * n + 8 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 4⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n+1, 2*n+4⟩) 0
  intro n; exact ⟨2*n+2, by
    rw [show 2 * n + 2 + 1 = 2 * n + 3 from by ring,
        show 2 * (2 * n + 2) + 4 = 4 * n + 8 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_612
