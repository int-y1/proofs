import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #325: [18/35, 20/3, 1/20, 49/2, 3/7]

Vector representation:
```
 1  2 -1 -1
 2 -1  1  0
-2  0 -1  0
-1  0  0  2
 0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_325

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a+2, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4 chain: (a+k, 0, 0, d) ->* (a, 0, 0, d+2*k)
theorem r4_chain : ∀ k a d, ⟨a+k, 0, 0, d⟩ [fm]⊢* ⟨a, 0, 0, d+2*k⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3 chain: (a+2*k, 0, c+k, 0) ->* (a, 0, c, 0) when a is even or a >= 2
-- Actually: (a+2*k, 0, k, 0) ->* (a, 0, 0, 0)
theorem r3_chain : ∀ k a, ⟨a+2*k, 0, k, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring]
  step fm
  apply stepStar_trans (ih _)
  finish

-- R2 chain when d=0: (a, k, c, 0) ->* (a+2*k, 0, c+k, 0)
theorem r2_chain : ∀ k a c, ⟨a, k, c, 0⟩ [fm]⊢* ⟨a+2*k, 0, c+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R2/R1 pair chain: (a, b+1, 0, k) ->* (a+3*k, b+k+1, 0, 0) when d >= 1 each step
-- More precisely: from (a, b+1, 0, d+k) do k pairs to get (a+3*k, b+k+1, 0, d)
theorem r2r1_chain : ∀ k a b d, ⟨a, b+1, 0, d+k⟩ [fm]⊢* ⟨a+3*k, b+k+1, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm  -- R2: (a+2, b, 1, (d+k)+1)
  rw [show (d + k) + 1 = d + k + 1 from rfl]
  step fm  -- R1: (a+3, b+2, 0, d+k)
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Main transition: (0, 0, 0, d+2) ->⁺ (0, 0, 0, 6*(d+1))
theorem main_trans (d : ℕ) : ⟨0, 0, 0, d+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6*(d+1)⟩ := by
  -- Phase 1: R5
  step fm  -- (0, 1, 0, d+1)
  -- Phase 2: d+1 R2/R1 pairs
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_trans (r2r1_chain (d+1) 0 0 0)
  rw [show 0 + 3 * (d + 1) = 3 * (d + 1) from by ring,
      show 0 + (d + 1) + 1 = d + 2 from by ring]
  -- Now at (3*(d+1), d+2, 0, 0)
  -- Phase 3: d+2 R2 steps
  apply stepStar_trans (r2_chain (d+2) (3*(d+1)) 0)
  rw [show 3 * (d + 1) + 2 * (d + 2) = 5 * d + 7 from by ring,
      show 0 + (d + 2) = d + 2 from by ring]
  -- Now at (5*d+7, 0, d+2, 0)
  -- Phase 4: d+2 R3 steps
  rw [show 5 * d + 7 = (3 * d + 3) + 2 * (d + 2) from by ring]
  apply stepStar_trans (r3_chain (d+2) (3*d+3))
  -- Now at (3*d+3, 0, 0, 0)
  -- Phase 5: R4 chain
  rw [show 3 * d + 3 = 0 + (3 * d + 3) from by ring]
  apply stepStar_trans (r4_chain (3*d+3) 0 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- First reach (0, 0, 0, 2) from c₀ = (1, 0, 0, 0)
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2⟩) (by execute fm 1)
  -- Use progress_nonhalt_simple with states (0, 0, 0, n+2) indexed by n : ℕ
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, 0, n+2⟩) 0
  intro n
  exact ⟨6*(n+1)-2, main_trans n⟩

end Sz22_2003_unofficial_325
