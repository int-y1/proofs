import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #313: [154/15, 1/3, 6/7, 25/2, 1/55, 3/5]

Vector representation:
```
 1 -1 -1  1  1
 0 -1  0  0  0
 1  1  0 -1  0
-1  0  2  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_313

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: convert a to c
theorem a_to_c : ∀ k c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c+2*k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show k + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R5 repeated: cancel c and e
theorem cancel_ce : ∀ k c, ⟨0, 0, c+k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show k + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (h _)
  finish

-- R1+R3 mixing loop: from (2*k, 1, n+1-k, 0, k) with k applications
-- We prove: (0, 1, n+1, 0, 0) ->* (2*(n+1), 1, 0, 0, n+1)
-- More generally: forall k, (2*j, 1, k, 0, j) ->* (2*(j+k), 1, 0, 0, j+k)
-- when k >= 0 (using R1 then R3 repeatedly)
theorem mix_loop : ∀ k j, ⟨2*j, 1, k, 0, j⟩ [fm]⊢* ⟨2*(j+k), 1, 0, 0, j+k⟩ := by
  intro k; induction' k with k h <;> intro j
  · simp only [Nat.add_zero]; exists 0
  -- R1 (b>=1, c>=1): (2*j, 1, k+1, 0, j) -> (2*j+1, 0, k, 1, j+1)
  step fm
  -- R3 (d>=1): (2*j+1, 0, k, 1, j+1) -> (2*j+2, 1, k, 0, j+1)
  step fm
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) from by ring]
  apply stepStar_trans (h (j+1))
  ring_nf; finish

-- Main transition: (0, 0, n+2, 0, 0) ->+ (0, 0, 3*n+3, 0, 0)
theorem main_trans (n : ℕ) : ⟨0, 0, n+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3*n+3, 0, 0⟩ := by
  -- R6: (0, 0, n+2, 0, 0) -> (0, 1, n+1, 0, 0)
  step fm
  -- Mixing loop: (0, 1, n+1, 0, 0) ->* (2*(n+1), 1, 0, 0, n+1)
  apply stepStar_trans (c₂ := ⟨2*(n+1), 1, 0, 0, n+1⟩)
  · have h := mix_loop (n+1) 0
    simp only [Nat.zero_add, Nat.mul_zero] at h; exact h
  -- R2 (b>=1, c=0): (2*(n+1), 1, 0, 0, n+1) -> (2*(n+1), 0, 0, 0, n+1)
  step fm
  -- a_to_c: (2*(n+1), 0, 0, 0, n+1) ->* (0, 0, 4*(n+1), 0, n+1)
  apply stepStar_trans (c₂ := ⟨0, 0, 4*(n+1), 0, n+1⟩)
  · have h := a_to_c (2*(n+1)) 0 (n+1)
    simp only [Nat.zero_add, (by ring : 2 * (2 * (n + 1)) = 4 * (n + 1))] at h; exact h
  -- cancel_ce: (0, 0, 4*(n+1), 0, n+1) ->* (0, 0, 3*(n+1), 0, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, 3*(n+1), 0, 0⟩)
  · have h := cancel_ce (n+1) (3*(n+1))
    simp only [(by ring : 3 * (n + 1) + (n + 1) = 4 * (n + 1))] at h; exact h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, n+2, 0, 0⟩) 0
  intro n
  refine ⟨3*n+1, ?_⟩
  show ⟨0, 0, n+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, (3*n+1)+2, 0, 0⟩
  rw [show (3 * n + 1) + 2 = 3 * n + 3 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_313
