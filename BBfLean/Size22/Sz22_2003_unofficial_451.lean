import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #451: [28/15, 1/3, 33/7, 25/2, 1/55, 3/5]

Vector representation:
```
 2 -1 -1  1  0
 0 -1  0  0  0
 0  1  0 -1  1
-1  0  2  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_451

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase: R1/R3 interleaved chain
-- From (a, 1, c+k, 0, e) to (a+2*k, 1, c, 0, e+k) via k rounds of R1,R3
theorem r1r3_chain : ∀ k, ∀ a c e, ⟨a, 1, c+k, 0, e⟩ [fm]⊢* ⟨a+2*k, 1, c, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm  -- R1: (a+2, 0, c+k, 1, e)
  step fm  -- R3: (a+2, 1, c+k, 0, e+1)
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase: R4 chain, convert a to c
-- From (a+k, 0, c, 0, e) to (a, 0, c+2*k, 0, e)
theorem r4_chain : ∀ k, ∀ a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [← Nat.add_assoc]
  step fm  -- R4: (a+k, 0, c+2, 0, e)
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase: R5 chain, drain c and e together
-- From (0, 0, c+k, 0, e+k) to (0, 0, c, 0, e)
theorem r5_chain : ∀ k, ∀ c e, ⟨0, 0, c+k, 0, e+k⟩ [fm]⊢* ⟨0, 0, c, 0, e⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R5: (0, 0, c+k, 0, e+k)
  exact h _ _

-- Main transition: (0, 0, c+2, 0, 0) ⊢⁺ (0, 0, 3*c+3, 0, 0)
theorem main_trans (c : ℕ) : ⟨0, 0, c+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3*c+3, 0, 0⟩ := by
  -- Phase 1: R6
  step fm  -- (0, 1, c+1, 0, 0)
  -- Phase 2: R1/R3 chain (c+1 rounds), then R2
  apply stepStar_trans (c₂ := ⟨2*(c+1), 1, 0, 0, c+1⟩)
  · have h := r1r3_chain (c+1) 0 0 0
    simp only [Nat.zero_add] at h; exact h
  step fm  -- R2: (2*(c+1), 0, 0, 0, c+1)
  -- Phase 3: R4 chain (2*(c+1) steps)
  apply stepStar_trans (c₂ := ⟨0, 0, 4*(c+1), 0, c+1⟩)
  · have h := r4_chain (2*(c+1)) 0 0 (c+1)
    simp only [Nat.zero_add, (by ring : 2 * (2 * (c + 1)) = 4 * (c + 1))] at h
    exact h
  -- Phase 4: R5 chain (c+1 steps)
  have h := r5_chain (c+1) (3*c+3) 0
  simp only [Nat.zero_add] at h
  rw [show 4 * (c + 1) = 3 * c + 3 + (c + 1) from by ring]
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c, q = ⟨0, 0, c+2, 0, 0⟩)
  · intro q ⟨c, hc⟩
    subst hc
    exact ⟨⟨0, 0, 3*c+3, 0, 0⟩, ⟨3*c+1, rfl⟩, main_trans c⟩
  · exact ⟨0, rfl⟩

end Sz22_2003_unofficial_451
