import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #259: [14/15, 1/3, 33/2, 125/11, 1/35, 3/5]

Vector representation:
```
 1 -1 -1  1  0
 0 -1  0  0  0
-1  1  0  0  1
 0  0  3  0 -1
 0  0 -1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_259

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1/R3 loop: alternating R1 and R3, k iterations
theorem r1r3_loop : ∀ k c d e, ⟨0, 1, c+k, d, e⟩ [fm]⊢* ⟨0, 1, c, d+k, e+k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih c (d + 1) (e + 1))
  ring_nf; finish

-- R4 loop: convert e to c (adding 3 per e)
theorem r4_loop : ∀ k c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c+3*k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · simp; exists 0
  step fm
  apply stepStar_trans (ih (c + 3) d)
  ring_nf; finish

-- R5 loop: cancel c and d together
theorem r5_loop : ∀ k c d, ⟨0, 0, c+k, d+k, 0⟩ [fm]⊢* ⟨0, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  exact ih c d

-- Main transition: (0, 0, n+2, 0, 0) →⁺ (0, 0, 2n+2, 0, 0)
theorem main_trans (n : ℕ) : ⟨0, 0, n+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*n+2, 0, 0⟩ := by
  -- Phase 1: R6
  step fm
  -- Phase 2: R1/R3 loop (n+1 times)
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (r1r3_loop (n+1) 0 0 0)
  simp only [Nat.zero_add]
  -- Phase 3: R2
  step fm
  -- Phase 4: R4 loop
  apply stepStar_trans (r4_loop (n+1) 0 (n+1))
  simp only [Nat.zero_add]
  -- Phase 5: R5 loop
  have h5 := r5_loop (n+1) (2*n+2) 0
  rw [show 2 * n + 2 + (n + 1) = 3 * (n + 1) from by ring,
      show 0 + (n + 1) = n + 1 from by ring] at h5
  exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n+3, 0, 0⟩) 0
  intro n
  exact ⟨2*n+1, by
    show ⟨0, 0, n+3, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, (2*n+1)+3, 0, 0⟩
    rw [show n + 3 = (n + 1) + 2 from by ring,
        show (2 * n + 1) + 3 = 2 * (n + 1) + 2 from by ring]
    exact main_trans (n+1)⟩

end Sz22_2003_unofficial_259
