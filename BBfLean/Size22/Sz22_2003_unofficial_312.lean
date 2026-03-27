import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #312: [154/15, 1/3, 3/7, 125/2, 1/55, 7/5]

Vector representation:
```
 1 -1 -1  1  1
 0 -1  0  0  0
 0  1  0 -1  0
-1  0  3  0  0
 0  0 -1  0 -1
 0  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_312

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R1,R3 chain: (0, 1, k, 0, 0) ->* (k, 1, 0, 0, k) via alternating R1 and R3
-- After each R1: a increases, b goes to 0, c decreases, d becomes 1, e increases
-- After each R3: d goes to 0, b becomes 1
theorem r1r3_chain : ∀ k a e, ⟨a, 1, k, 0, e⟩ [fm]⊢* ⟨a+k, 1, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  -- State: (a, 1, k+1, 0, e)
  -- R1: (a+1, 0, k, 1, e+1)
  step fm
  -- R3: (a+1, 1, k, 0, e+1)
  step fm
  apply stepStar_trans (ih (a+1) (e+1))
  rw [show a + 1 + k = a + (k + 1) from by ring,
      show e + 1 + k = e + (k + 1) from by ring]
  finish

-- R4 chain: (k, 0, c, 0, e) ->* (0, 0, c+3*k, 0, e)
theorem a_to_c : ∀ k c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+3*k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  -- State: (k+1, 0, c, 0, e)
  -- R4: (k, 0, c+3, 0, e)
  step fm
  apply stepStar_trans (ih (c+3) e)
  rw [show c + 3 + 3 * k = c + 3 * (k + 1) from by ring]
  finish

-- R5 chain: (0, 0, c+k, 0, k) ->* (0, 0, c, 0, 0)
theorem r5_chain : ∀ k c, ⟨0, 0, c+k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  -- State: (0, 0, c+k+1, 0, k+1)
  -- R5: (0, 0, c+k, 0, k)
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  exact ih c

-- Main transition: (0, 0, n+2, 0, 0) ->+ (0, 0, 2*(n+1), 0, 0) = (0, 0, 2*n+2, 0, 0)
-- i.e., from c₀ = n+2 to 2*(n+2) - 2 = 2*n+2
theorem main_trans (n : ℕ) : ⟨0, 0, n+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*n+2, 0, 0⟩ := by
  -- Phase 1: R6: (0, 0, n+1+1, 0, 0) -> (0, 0, n+1, 1, 0)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, n+1, 1, 0⟩)
  · show fm ⟨0, 0, (n+1)+1, 0, 0⟩ = some ⟨0, 0, n+1, 0+1, 0⟩; simp [fm]
  -- Phase 2: R3: (0, 0, n+1, 1, 0) -> (0, 1, n+1, 0, 0)
  apply stepStar_trans (c₂ := ⟨0, 1, n+1, 0, 0⟩)
  · apply step_stepStar
    show fm ⟨0, 0, n+1, 0+1, 0⟩ = some ⟨0, 0+1, n+1, 0, 0⟩; simp [fm]
  -- Phase 3: R1,R3 chain: (0, 1, n+1, 0, 0) ->* (n+1, 1, 0, 0, n+1)
  apply stepStar_trans (c₂ := ⟨n+1, 1, 0, 0, n+1⟩)
  · have h := r1r3_chain (n+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 4: R2: (n+1, 1, 0, 0, n+1) -> (n+1, 0, 0, 0, n+1)
  apply stepStar_trans (c₂ := ⟨n+1, 0, 0, 0, n+1⟩)
  · apply step_stepStar
    show fm ⟨n+1, 0+1, 0, 0, n+1⟩ = some ⟨n+1, 0, 0, 0, n+1⟩; simp [fm]
  -- Phase 5: R4 chain: (n+1, 0, 0, 0, n+1) ->* (0, 0, 3*(n+1), 0, n+1)
  apply stepStar_trans (c₂ := ⟨0, 0, 3*(n+1), 0, n+1⟩)
  · have h := a_to_c (n+1) 0 (n+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 6: R5 chain: (0, 0, 3*(n+1), 0, n+1) = (0, 0, 2*(n+1) + (n+1), 0, n+1)
  --   ->* (0, 0, 2*(n+1), 0, 0)
  have h := r5_chain (n+1) (2*(n+1))
  rw [show 2 * (n + 1) + (n + 1) = 3 * (n + 1) from by ring,
      show 2 * (n + 1) = 2 * n + 2 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, n+2, 0, 0⟩) 1
  intro n
  exact ⟨2*n, main_trans n⟩

end Sz22_2003_unofficial_312
