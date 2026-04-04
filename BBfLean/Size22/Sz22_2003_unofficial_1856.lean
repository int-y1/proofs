import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1856: [9/35, 20/3, 1/20, 343/2, 3/7]

Vector representation:
```
 0  2 -1 -1
 2 -1  1  0
-2  0 -1  0
-1  0  0  3
 0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1856

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a+2, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+3⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4 chain: drain a, accumulate d.
theorem r4_chain : ∀ k, ∀ d, ⟨k, 0, 0, d⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 3))
    ring_nf; finish

-- R2 chain: drain b, accumulate a and c (d = 0).
theorem r2_chain : ∀ b, ∀ a c, ⟨a, b, c, 0⟩ [fm]⊢* ⟨a + 2 * b, 0, c + b, 0⟩ := by
  intro b; induction' b with b ih <;> intro a c
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 2) (c + 1))
    ring_nf; finish

-- R3 chain: drain c by 2 from a (b = 0, d = 0).
theorem r3_chain : ∀ c, ∀ a, ⟨a + 2 * c, 0, c, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro c; induction' c with c ih <;> intro a
  · exists 0
  · rw [show a + 2 * (c + 1) = (a + 2 * c) + 2 from by ring]
    step fm
    exact ih a

-- Interleave R1/R2: from (a, b, 1, n+1), alternate R1 and R2 until d = 0.
theorem interleave : ∀ n, ∀ a b, ⟨a, b, 1, n + 1⟩ [fm]⊢* ⟨a + 2 * n, b + n + 2, 0, 0⟩ := by
  intro n; induction' n with n ih <;> intro a b
  · step fm; finish
  · rw [show (n + 1) + 1 = n + 2 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 2) (b + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, D+2) ⊢⁺ (0, 0, 0, 6*D+6)
theorem main_trans : ∀ D, ⟨0, 0, 0, D + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * D + 6⟩ := by
  intro D
  -- R5: (0, 0, 0, D+2) -> (0, 1, 0, D+1)
  step fm
  -- R2: (0, 1, 0, D+1) -> (2, 0, 1, D+1)
  step fm
  -- Interleave: (2, 0, 1, D+1) ->* (2D+2, D+2, 0, 0)
  show ⟨2, 0, 1, D + 1⟩ [fm]⊢* ⟨0, 0, 0, 6 * D + 6⟩
  apply stepStar_trans (interleave D 2 0)
  -- R2 chain: (2D+2, D+2, 0, 0) ->* (4D+6, 0, D+2, 0)
  rw [show 2 + 2 * D = 2 * D + 2 from by ring,
      show 0 + D + 2 = D + 2 from by ring]
  apply stepStar_trans (r2_chain (D + 2) (2 * D + 2) 0)
  rw [show 2 * D + 2 + 2 * (D + 2) = 4 * D + 6 from by ring,
      show 0 + (D + 2) = D + 2 from by ring]
  -- R3 chain: (4D+6, 0, D+2, 0) ->* (2D+2, 0, 0, 0)
  rw [show 4 * D + 6 = (2 * D + 2) + 2 * (D + 2) from by ring]
  apply stepStar_trans (r3_chain (D + 2) (2 * D + 2))
  -- R4 chain: (2D+2, 0, 0, 0) ->* (0, 0, 0, 6D+6)
  rw [show (2 * D + 2 : ℕ) = 2 * D + 2 from by ring]
  apply stepStar_trans (r4_chain (2 * D + 2) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2⟩) 1
  intro n; exists 6 * n + 4
  show ⟨0, 0, 0, n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * n + 4 + 2⟩
  rw [show 6 * n + 4 + 2 = 6 * n + 6 from by ring]
  exact main_trans n
