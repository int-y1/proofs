import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #54: [1/15, 9/539, 28/3, 275/2, 7/5]

Vector representation:
```
 0 -1 -1  0  0
 0  2  0 -2 -1
 2 -1  0  1  0
-1  0  2  0  1
 0  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_54

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- Phase 1: R4 chain. (a+k, 0, c, 0, e) ->* (a, 0, c+2*k, 0, e+k)
theorem r4_chain : ∀ k, ∀ a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2 round: R5,R5,R2,R1,R1. (0, 0, c+4, 0, e+1) ->* (0, 0, c, 0, e)
theorem phase2_round : ∀ k, ∀ c e, ⟨0, 0, c+4*k, 0, e+k⟩ [fm]⊢* ⟨0, 0, c, 0, e⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + 4 * (k + 1) = (c + 4 * k) + 4 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  -- (0, 0, (c+4*k)+4, 0, (e+k)+1)
  -- R5: (0, 0, (c+4*k)+3, 1, (e+k)+1)
  step fm
  -- R5: (0, 0, (c+4*k)+2, 2, (e+k)+1)
  step fm
  -- R2: (0, 2, (c+4*k)+2, 0, e+k)
  step fm
  -- R1: (0, 1, (c+4*k)+1, 0, e+k)
  rw [show (c + 4 * k) + 2 = ((c + 4 * k) + 1) + 1 from by ring]
  step fm
  -- R1: (0, 0, c+4*k, 0, e+k)
  rw [show (c + 4 * k) + 1 = (c + 4 * k) + 1 from by ring]
  step fm
  exact h _ _

-- Phase 2 tail: (0, 0, 2, 0, e+1) -> (0, 2, 0, 0, e) via R5,R5,R2
theorem phase2_tail : ∀ e, ⟨0, 0, 2, 0, e+1⟩ [fm]⊢* ⟨0, 2, 0, 0, e⟩ := by
  intro e
  step fm; step fm; step fm
  finish

-- Phase 3: R3,R3,R2 chain. (a, 2, 0, 0, e+1) ->* (a+4, 2, 0, 0, e)
theorem r3r3r2_chain : ∀ k, ∀ a, ⟨a, 2, 0, 0, k⟩ [fm]⊢* ⟨a+4*k, 2, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a
  · exists 0
  rw [show k + 1 = k + 1 from rfl]
  -- (a, 2, 0, 0, k+1)
  -- R3: (a+2, 1, 0, 1, k+1)
  step fm
  -- R3: (a+4, 0, 0, 2, k+1)
  step fm
  -- R2: (a+4, 2, 0, 0, k)
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- Phase 3 tail: (a, 2, 0, 0, 0) -> (a+4, 0, 0, 2, 0) via R3,R3
theorem phase3_tail : ∀ a, ⟨a, 2, 0, 0, 0⟩ [fm]⊢* ⟨a+4, 0, 0, 2, 0⟩ := by
  intro a
  step fm; step fm
  finish

-- Phase 4: (a+1, 0, 0, 2, 0) -> (a, 0, 0, 0, 0) via R4,R2,R1,R1
theorem phase4 : ∀ a, ⟨a+1, 0, 0, 2, 0⟩ [fm]⊢* ⟨a, 0, 0, 0, 0⟩ := by
  intro a
  -- R4: (a, 0, 2, 2, 1)
  step fm
  -- R2: (a, 2, 2, 0, 0)
  step fm
  -- R1: (a, 1, 1, 0, 0)
  step fm
  -- R1: (a, 0, 0, 0, 0)
  step fm
  finish

-- Main transition: (2*n+1, 0, 0, 0, 0) ⊢⁺ (4*n+3, 0, 0, 0, 0)
theorem main_trans (n : ℕ) : ⟨2*n+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨4*n+3, 0, 0, 0, 0⟩ := by
  -- Phase 1: R4 chain, (2*n+1) steps
  -- (2*n+1, 0, 0, 0, 0) ->* (0, 0, 2*(2*n+1), 0, 2*n+1) = (0, 0, 4*n+2, 0, 2*n+1)
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (2*n+1) 0 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Now at (0, 0, 2*(2*n+1), 0, 2*n+1)
  -- Phase 2: n rounds of R5,R5,R2,R1,R1
  rw [show 2 * (2 * n + 1) = 4 * n + 2 from by ring]
  apply stepStar_stepPlus_stepPlus
  · have h := phase2_round n 2 (n+1)
    simp only [(by ring : 2 + 4 * n = 4 * n + 2),
               (by ring : n + 1 + n = 2 * n + 1)] at h; exact h
  -- Phase 2 tail: (0, 0, 2, 0, n+1) ->* (0, 2, 0, 0, n)
  apply stepStar_stepPlus_stepPlus
  · exact phase2_tail n
  -- Phase 3: n rounds of R3,R3,R2
  -- (0, 2, 0, 0, n) ->* (4*n, 2, 0, 0, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := r3r3r2_chain n 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3 tail: (4*n, 2, 0, 0, 0) ->* (4*n+4, 0, 0, 2, 0)
  apply stepStar_stepPlus_stepPlus
  · exact phase3_tail (4*n)
  -- Phase 4: (4*n+4, 0, 0, 2, 0) -> (4*n+3, 0, 0, 0, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨(4*n+3)+1, 0, 0, 2, 0⟩ = some ⟨4*n+3, 0, 2, 2, 1⟩
    simp only [(by ring : 4 * n + 3 + 1 = 4 * n + 4)]
    rfl
  step fm; step fm; step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨2*n+1, 0, 0, 0, 0⟩) 0
  intro n
  exists 2*n+1
  show ⟨2*n+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨2*(2*n+1)+1, 0, 0, 0, 0⟩
  simp only [(by ring : 2 * (2 * n + 1) + 1 = 4 * n + 3)]
  exact main_trans n

end Sz22_2003_unofficial_54
