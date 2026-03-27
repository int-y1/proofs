import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #117: [1/315, 55/2, 14/65, 507/11, 5/7]

Vector representation:
```
 0 -2 -1 -1  0  0
-1  0  1  0  1  0
 1  0 -1  1  0 -1
 0  1  0  0 -1  2
 0  0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_117

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d+1, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f+2⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- Phase 2: R4 repeated: convert e to b, adding 2 to f each time
-- (0, b, 0, d, e+k, f) ->* (0, b+k, 0, d, e, f+2*k)
theorem e_to_b : ∀ k, ∀ b d e f, ⟨0, b, 0, d, e+k, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f+2*k⟩ := by
  intro k; induction' k with k h <;> intro b d e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Phase 3: R5+R1 cleanup: (0, 2*k+1, 0, 2*k+1, 0, f) ->* (0, 1, 1, 0, 0, f)
theorem cleanup : ∀ k, ∀ f, ⟨0, 2*k+1, 0, 2*k+1, 0, f⟩ [fm]⊢* ⟨0, 1, 1, 0, 0, f⟩ := by
  intro k; induction' k with k h <;> intro f
  · step fm; finish
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (h _)
  finish

-- Phase 4: R3+R2 chain: (0, 1, 1, d, d, f+k) ->* (0, 1, 1, d+k, d+k, f)
-- Each iteration: R3 then R2
theorem r3r2_chain : ∀ k, ∀ d f, ⟨0, 1, 1, d, d, f+k⟩ [fm]⊢* ⟨0, 1, 1, d+k, d+k, f⟩ := by
  intro k; induction' k with k h <;> intro d f
  · exists 0
  rw [show f + (k + 1) = (f + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Main transition: (0, 1, 1, 2*m, 2*m, 0) ->+ (0, 1, 1, 4*m, 4*m, 0) for m >= 1
theorem main_trans (m : ℕ) : ⟨0, 1, 1, 2*(m+1), 2*(m+1), 0⟩ [fm]⊢⁺ ⟨0, 1, 1, 4*(m+1), 4*(m+1), 0⟩ := by
  -- Phase 1: R4, R1 (2 steps)
  rw [show 2 * (m + 1) = (2 * m + 1) + 1 from by ring]
  step fm; step fm
  -- Now at: (0, 0, 0, 2*m+1, 2*m+1, 2)
  -- Phase 2: e_to_b (2*m+1 steps)
  apply stepStar_trans (c₂ := ⟨0, 2*m+1, 0, 2*m+1, 0, 2*(2*(m+1))⟩)
  · have h := e_to_b (2*m+1) 0 (2*m+1) 0 2
    simp only [Nat.zero_add, (by ring : 2 + 2 * (2 * m + 1) = 2 * (2 * (m + 1)))] at h
    exact h
  -- Phase 3: cleanup (2*m+1 steps)
  apply stepStar_trans (c₂ := ⟨0, 1, 1, 0, 0, 4*(m+1)⟩)
  · rw [show 2 * (2 * (m + 1)) = 4 * (m + 1) from by ring]
    exact cleanup m (4*(m+1))
  -- Phase 4: r3r2_chain (4*(m+1) steps)
  have h := r3r2_chain (4*(m+1)) 0 0
  simp only [Nat.zero_add] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 1, 2, 2, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 1, 1, 2*(n+1), 2*(n+1), 0⟩) 0
  intro n
  exists n + n + 1
  show ⟨0, 1, 1, 2*(n+1), 2*(n+1), 0⟩ [fm]⊢⁺ ⟨0, 1, 1, 2*((n+n+1)+1), 2*((n+n+1)+1), 0⟩
  have h := main_trans n
  simp only [(by ring : 4 * (n + 1) = 2 * ((n + n + 1) + 1))] at h
  exact h

end Sz22_2003_unofficial_117
