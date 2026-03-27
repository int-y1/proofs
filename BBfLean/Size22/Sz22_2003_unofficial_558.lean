import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #558: [308/15, 3/7, 1/3, 25/2, 1/55, 7/5]

Vector representation:
```
 2 -1 -1  1  1
 0  1  0 -1  0
 0 -1  0  0  0
-1  0  2  0  0
 0  0 -1  0 -1
 0  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_558

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: convert a to c
theorem a_to_c : ∀ k c, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro c
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _); ring_nf; finish

-- R5 repeated: cancel c and e
theorem cancel_ce : ∀ k c, ⟨0, 0, c+k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by omega]
  step fm; apply stepStar_trans (h _); finish

-- R1+R2 chain then R2+R3: (a, 1, k+1, 0, e) ->* (a+2*(k+1), 0, 0, 0, e+k+1)
theorem r1r2r3_chain : ∀ k a e, ⟨a, 1, k+1, 0, e⟩ [fm]⊢* ⟨a+2*(k+1), 0, 0, 0, e+k+1⟩ := by
  intro k; induction' k with k h <;> intro a e
  · step fm; step fm; step fm; ring_nf; finish
  step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Phase 3: (0, 0, C+2, 0, 0) ->⁺ (2*(C+1), 0, 0, 0, C+1)
theorem phase3 : ⟨0, 0, C+2, 0, 0⟩ [fm]⊢⁺ ⟨2*(C+1), 0, 0, 0, C+1⟩ := by
  -- R6: -> (0, 0, C+1, 1, 0)
  -- R2: -> (0, 1, C+1, 0, 0)
  step fm; step fm
  apply stepStar_trans (r1r2r3_chain C 0 0)
  ring_nf; finish

-- Main transition: (2*(n+1), 0, 0, 0, n+1) ->⁺ (2*(3*n+2), 0, 0, 0, 3*n+2)
theorem main_trans (n : ℕ) : ⟨2*(n+1), 0, 0, 0, n+1⟩ [fm]⊢⁺ ⟨2*(3*n+2), 0, 0, 0, 3*n+2⟩ := by
  -- Phase 1: R4 chain: (2*(n+1), 0, 0, 0, n+1) ->* (0, 0, 4*(n+1), 0, n+1)
  rw [show 2 * (n + 1) = 0 + 2 * (n + 1) from by omega,
      show (0 : ℕ) = 0 + 2 * 0 from by omega]
  apply stepStar_stepPlus_stepPlus (a_to_c (2 * (n + 1)) (2 * 0))
  -- (0, 0, 4*(n+1), 0, n+1)
  -- Phase 2: R5 chain: cancel (n+1) copies
  rw [show 2 * 0 + 2 * (2 * (n + 1)) = 3 * (n + 1) + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (cancel_ce (n + 1) (3 * (n + 1)))
  -- (0, 0, 3*(n+1), 0, 0) = (0, 0, (3*n+1)+2, 0, 0)
  -- Phase 3
  rw [show 3 * (n + 1) = (3 * n + 1) + 2 from by ring]
  have h := @phase3 (3 * n + 1)
  rw [show 2 * (3 * n + 1 + 1) = 2 * (3 * n + 2) from by ring,
      show 3 * n + 1 + 1 = 3 * n + 2 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2*(n+1), 0, 0, 0, n+1⟩) 0
  intro n; exact ⟨3*n+1, main_trans n⟩
