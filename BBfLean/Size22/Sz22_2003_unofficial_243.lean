import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #243: [11/105, 4/3, 15/22, 49/2, 33/7]

Vector representation:
```
 0 -1 -1 -1  1
 2 -1  0  0  0
-1  1  1  0 -1
-1  0  0  2  0
 0  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_243

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: convert a to d
theorem a_to_d : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5+R1 chain
theorem r5r1_chain : ∀ k c d e, ⟨0, 0, c+k, d+2*k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = c + k + 1 from by ring,
      show d + 2 * (k + 1) = (d + 2 * k + 1) + 1 from by ring]
  step fm
  rw [show c + k + 1 = (c + k) + 1 from by ring,
      show d + 2 * k + 1 = (d + 2 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3+R2 chain
theorem r3r2_chain : ∀ k a c e, ⟨a+1, 0, c, 0, e+k⟩ [fm]⊢* ⟨a+k+1, 0, c+k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: (2*(k+1), 0, 2*k+1, 0, 0) ->+ (4*k+4, 0, 4*k+3, 0, 0)
theorem main_trans (k : ℕ) : ⟨2*k+2, 0, 2*k+1, 0, 0⟩ [fm]⊢⁺ ⟨4*k+4, 0, 4*k+3, 0, 0⟩ := by
  -- First R4 step to get stepPlus
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm
  -- Now: (2*k+1, 0, 2*k+1, 2, 0)
  -- Remaining R4 steps
  apply stepStar_trans (c₂ := ⟨0, 0, 2*k+1, 4*k+4, 0⟩)
  · have h := a_to_d (2*k+1) 0 (2*k+1) 2
    simp only [Nat.zero_add, (by ring : 2 + 2 * (2 * k + 1) = 4 * k + 4)] at h
    exact h
  -- R5+R1 chain
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 2, 4*k+2⟩)
  · have h := r5r1_chain (2*k+1) 0 2 0
    simp only [Nat.zero_add, (by ring : 2 + 2 * (2 * k + 1) = 4 * k + 4),
               (by ring : 0 + 2 * (2 * k + 1) = 4 * k + 2)] at h
    exact h
  -- (0, 0, 0, 2, 4k+2) -> R5 -> R2 -> R3 -> R1 -> (1, 0, 0, 0, 4k+3)
  step fm
  step fm
  rw [show 4 * k + 3 = (4 * k + 2) + 1 from by ring]
  step fm
  step fm
  -- (1, 0, 0, 0, 4k+3) -> R3 -> R2 -> (2, 0, 1, 0, 4k+2)
  rw [show 4 * k + 3 = (4 * k + 2) + 1 from by ring]
  step fm
  step fm
  -- R3+R2 chain: (2, 0, 1, 0, 4k+2) ->* (4k+4, 0, 4k+3, 0, 0)
  have h := r3r2_chain (4*k+2) 1 1 0
  simp only [(by ring : 1 + (4 * k + 2) = 4 * k + 3),
             (by ring : 0 + (4 * k + 2) = 4 * k + 2)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨2*n+2, 0, 2*n+1, 0, 0⟩) 0
  intro n
  exists 2*n+1
  show ⟨2*n+2, 0, 2*n+1, 0, 0⟩ [fm]⊢⁺ ⟨2*(2*n+1)+2, 0, 2*(2*n+1)+1, 0, 0⟩
  simp only [(by ring : 2 * (2 * n + 1) + 2 = 4 * n + 4),
             (by ring : 2 * (2 * n + 1) + 1 = 4 * n + 3)]
  exact main_trans n

end Sz22_2003_unofficial_243
