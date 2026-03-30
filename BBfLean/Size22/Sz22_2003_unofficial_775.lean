import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #775: [35/6, 55/2, 4/385, 3/5, 4/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  1
 2  0 -1 -1 -1
 0  1 -1  0  0
 2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_775

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

-- Phase 1: R4 chain. Move c to b when a=0, d=0, e=0.
theorem c_to_b : ∀ k b, ⟨0, b, k, 0, 0⟩ [fm]⊢* ⟨0, b + k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

-- Phase 1': R4 chain when e >= 1. Move c to b when a=0, d=0.
theorem c_to_b' : ∀ k b, ⟨0, b, k, 0, e + 1⟩ [fm]⊢* ⟨0, b + k, 0, 0, e + 1⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

-- Phase 3: R1,R1,R3 chain. (2, 2k+1, c, d, k) ->* (2, 1, c+k, d+k, 0)
-- Rewrite: (2, b+2, c, d, k+1) with b = 2k-1... let me try a different formulation.
-- Each round: (2, b+2, c, d, e+1) -> R1 (1, b+1, c+1, d+1, e+1) -> R1 (0, b, c+2, d+2, e+1)
--   -> R3 (2, b, c+1, d+1, e)
-- So we go from e+1 to e, consuming 2 from b, gaining 1 each to c and d.
theorem r1r1r3_chain : ∀ k c d, ⟨2, 2 * k + 1, c, d, k⟩ [fm]⊢* ⟨2, 1, c + k, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · simp; exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih (c + 1) (d + 1))
    ring_nf; finish

-- Phase 5: R3,R2,R2 chain. (0, 0, c+1, k+1, e+1) ->* (0, 0, c+k+2, 0, e+k+2)
theorem r3r2r2_chain : ∀ k c e, ⟨0, 0, c + 1, k + 1, e + 1⟩ [fm]⊢* ⟨0, 0, c + k + 2, 0, e + k + 2⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · step fm; step fm; step fm; finish
  · step fm
    step fm
    step fm
    rw [show c + 2 = (c + 1) + 1 from by ring,
        show e + 2 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 1) (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, 2n+1, 0, n+1) ->+ (0, 0, 2n+3, 0, n+2)
theorem main_trans : ⟨0, 0, 2 * n + 1, 0, n + 1⟩ [fm]⊢⁺ ⟨0, 0, 2 * n + 3, 0, n + 2⟩ := by
  -- Phase 1: c_to_b': (0, 0, 2n+1, 0, n+1) ->* (0, 2n+1, 0, 0, n+1)
  rw [show n + 1 = n + 1 from rfl,
      show (0 : ℕ) = 0 from rfl]
  apply stepStar_stepPlus_stepPlus (c_to_b' (2 * n + 1) 0 (e := n))
  -- Now at: (0, 2n+1, 0, 0, n+1)
  -- Phase 2: R5: (0, 2n+1, 0, 0, n+1) -> (2, 2n+1, 0, 0, n)
  step fm
  rw [show 0 + (2 * n + 1) = 2 * n + 1 from by ring]
  -- Phase 3: R1,R1,R3 chain: (2, 2n+1, 0, 0, n) ->* (2, 1, n, n, 0)
  apply stepStar_trans (r1r1r3_chain n 0 0)
  rw [show 0 + n = n from by ring]
  -- Phase 3b: R1: (2, 1, n, n, 0) -> (1, 0, n+1, n+1, 0)
  step fm
  -- Phase 4: R2: (1, 0, n+1, n+1, 0) -> (0, 0, n+2, n+1, 1)
  step fm
  -- Phase 5: R3,R2,R2 chain: (0, 0, n+2, n+1, 1) ->* (0, 0, 2n+3, 0, n+2)
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain n (n + 1) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * n + 1, 0, n + 1⟩) 0
  intro n; exists n + 1; exact main_trans
