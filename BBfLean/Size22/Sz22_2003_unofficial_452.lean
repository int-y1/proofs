import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #452: [28/15, 1/3, 363/2, 5/11, 1/35, 3/5]

Vector representation:
```
 2 -1 -1  1  0
 0 -1  0  0  0
-1  1  0  0  2
 0  0  1  0 -1
 0  0 -1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_452

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1: R1,R3 interleaved chain
-- From (a, 1, k+1, d, e) with k rounds remaining:
-- Each round: R1 then R3, consuming 1 from c, adding 1 to d and 2 to e, net +1 to a
-- Final round (when c becomes 1): just R1
-- Overall: (0, 1, c+1, 0, 0) ->* (c+2, 0, 0, c+1, 2*c)
theorem r1r3_chain : ∀ k a d e, ⟨a, 1, k+1, d, e⟩ [fm]⊢* ⟨a+k+2, 0, 0, d+k+1, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · -- k=0: just R1
    step fm; finish
  · -- k+1: R1, R3, then IH
    rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm  -- R1: (a+2, 0, k+1, d+1, e)
    step fm  -- R3: (a+1, 1, k+1, d+1, e+2)
    apply stepStar_trans (h _ _ _)
    ring_nf; finish

-- Phase 2: R3,R2 chain: drain a, each step adding 2 to e
-- (a+k, 0, 0, d, e) ->* (a, 0, 0, d, e+2*k)
-- Actually: R3 gives (a+k-1, 1, 0, d, e+2), R2 gives (a+k-1, 0, 0, d, e+2)
theorem r3r2_chain : ∀ k a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm  -- R3: (a+k, 1, 0, d, e+2)
  step fm  -- R2: (a+k, 0, 0, d, e+2)
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 3: R4 chain: transfer e to c
-- (0, 0, c, d, e+k) ->* (0, 0, c+k, d, e)
theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c+k, d, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R4: (0, 0, c+1, d, e+k)
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 4: R5 chain: subtract d from c
-- (0, 0, c+k, d+k, 0) ->* (0, 0, c, d, 0)
theorem r5_chain : ∀ k c d, ⟨0, 0, c+k, d+k, 0⟩ [fm]⊢* ⟨0, 0, c, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm  -- R5: (0, 0, c+k, d+k, 0)
  exact h _ _

-- Main transition: (0, 0, c+2, 0, 0) ⊢⁺ (0, 0, 3*c+3, 0, 0)
theorem main_trans (c : ℕ) : ⟨0, 0, c+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3*c+3, 0, 0⟩ := by
  -- Step 1: R6 + R1,R3 chain: (0, 0, c+2, 0, 0) ⊢⁺ (c+2, 0, 0, c+1, 2*c)
  apply stepPlus_stepStar_stepPlus (c₂ := ⟨c+2, 0, 0, c+1, 2*c⟩)
  · rw [show c + 2 = (c + 1) + 1 from by ring]
    step fm  -- R6: (0, 1, c+1, 0, 0)
    have h := r1r3_chain c 0 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Step 3: R3,R2 chain -> (0, 0, 0, c+1, 4*c+4)
  apply stepStar_trans (c₂ := ⟨0, 0, 0, c+1, 4*c+4⟩)
  · have h := r3r2_chain (c+2) 0 (c+1) (2*c)
    simp only [Nat.zero_add, (by ring : 2 * c + 2 * (c + 2) = 4 * c + 4)] at h
    exact h
  -- Step 4: R4 chain -> (0, 0, 4*c+4, c+1, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, 4*c+4, c+1, 0⟩)
  · have h := r4_chain (4*c+4) 0 (c+1) 0
    simp only [Nat.zero_add] at h; exact h
  -- Step 5: R5 chain -> (0, 0, 3*c+3, 0, 0)
  have h := r5_chain (c+1) (3*c+3) 0
  simp only [Nat.zero_add, (by ring : 3 * c + 3 + (c + 1) = 4 * c + 4)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, n+2, 0, 0⟩) 0
  intro n
  exists 3*n+1
  exact main_trans n

end Sz22_2003_unofficial_452
