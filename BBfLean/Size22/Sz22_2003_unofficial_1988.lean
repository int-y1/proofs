import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1988: [99/35, 4/5, 5/6, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  1
 2  0 -1  0  0
-1 -1  1  0  0
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1988

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 repeated: move e to d.
theorem e_to_d : ∀ e, ∀ d, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + e, 0⟩ := by
  intro e; induction' e with e ih <;> intro d
  · exists 0
  · rw [show d + (e + 1) = (d + 1) + e from by ring]
    step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- Spiral: (R1, R3) interleaved.
theorem spiral : ∀ k, ∀ b e, ⟨k, b, 1, k, e⟩ [fm]⊢* ⟨0, b + k, 1, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show k + 1 = Nat.succ k from rfl]
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) (e + 1))
    ring_nf; finish

-- Drain: (R3, R2) interleaved.
theorem drain : ∀ k, ∀ a e, ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show k + 1 = Nat.succ k from rfl]
    step fm
    step fm
    rw [show a + 1 + (k + 1) = (a + 1) + 1 + k from by ring]
    exact ih (a + 1) e

-- Main transition
theorem main_trans : ∀ n, ⟨n + 1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, n + 1⟩ := by
  intro n
  -- e_to_d: (n+1, 0, 0, 0, n) ->* (n+1, 0, 0, n, 0)
  apply stepStar_stepPlus_stepPlus (e_to_d n 0 (a := n + 1))
  rw [show (0 : ℕ) + n = n from by ring]
  -- R5: (n+1, 0, 0, n, 0) -> (n, 0, 1, n, 1)
  step fm
  -- spiral: (n, 0, 1, n, 1) ->* (0, n, 1, 0, n+1)
  apply stepStar_trans (spiral n 0 1)
  rw [show (0 : ℕ) + n = n from by ring, show 1 + n = n + 1 from by ring]
  -- R2: (0, n, 1, 0, n+1) -> (2, n, 0, 0, n+1)
  step fm
  -- drain: (2, n, 0, 0, n+1) ->* (n+2, 0, 0, 0, n+1)
  show ⟨2, n, 0, 0, n + 1⟩ [fm]⊢* ⟨n + 2, 0, 0, 0, n + 1⟩
  rw [show (2 : ℕ) = 1 + 1 from by ring, show n + 2 = 1 + 1 + n from by ring]
  exact drain n 1 (n + 1)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, n⟩) 0
  intro n; exists n + 1; exact main_trans n
