import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #116: [1/315, 14/55, 65/2, 363/13, 5/7]

Vector representation:
```
 0 -2 -1 -1  0  0
 1  0 -1  1 -1  0
-1  0  1  0  0  1
 0  1  0  0  2 -1
 0  0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_116

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d+1, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+2, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- Phase 1: R2/R3 alternating chain
-- Each pair: (0, 1, 1, d, e+1, f) →R2 (1, 1, 0, d+1, e, f) →R3 (0, 1, 1, d+1, e, f+1)
theorem r2r3_chain : ∀ j, ∀ d f,
    ⟨0, 1, 1, d, j, f⟩ [fm]⊢* ⟨0, 1, 1, d + j, 0, f + j⟩ := by
  intro j; induction' j with j ih <;> intro d f
  · exists 0
  · rw [show d + (j + 1) = (d + 1) + j from by ring,
        show f + (j + 1) = (f + 1) + j from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Phase 3: R4 chain - convert f to b and 2e
theorem r4_chain : ∀ j, ∀ b d e,
    ⟨0, b, 0, d, e, j⟩ [fm]⊢* ⟨0, b + j, 0, d, e + 2 * j, 0⟩ := by
  intro j; induction' j with j ih <;> intro b d e
  · exists 0
  · rw [show b + (j + 1) = (b + 1) + j from by ring,
        show e + 2 * (j + 1) = (e + 2) + 2 * j from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase 4: R5/R1 drain pairs, each removing 2 from b and d
theorem r5r1_drain : ∀ k, ∀ e,
    ⟨0, 2 * k + 1, 0, 2 * k + 1, e, 0⟩ [fm]⊢* ⟨0, 1, 0, 1, e, 0⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm
    exact ih _

-- Main transition: (0, 1, 1, 0, 2*(n+1), 0) →⁺ (0, 1, 1, 0, 4*(n+1), 0)
theorem main_trans (n : ℕ) :
    ⟨0, 1, 1, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨0, 1, 1, 0, 4 * n + 4, 0⟩ := by
  -- Phase 1: R2/R3 chain
  -- (0, 1, 1, 0, 2*n+2, 0) →* (0, 1, 1, 2*n+2, 0, 2*n+2)
  apply stepStar_stepPlus_stepPlus
  · have h := r2r3_chain (2 * n + 2) 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 2: R4, R1
  -- (0, 1, 1, 2*n+2, 0, 2*n+2) → (0, 2, 1, 2*n+2, 2, 2*n+1) → (0, 0, 0, 2*n+1, 2, 2*n+1)
  step fm; step fm
  -- Phase 3: R4 chain
  -- (0, 0, 0, 2*n+1, 2, 2*n+1) →* (0, 2*n+1, 0, 2*n+1, 4*n+4, 0)
  apply stepStar_trans
  · have h := r4_chain (2 * n + 1) 0 (2 * n + 1) 2
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * (2 * n + 1) = 4 * n + 4 from by ring] at h
    exact h
  -- Phase 4: R5/R1 drain
  -- (0, 2*n+1, 0, 2*n+1, 4*n+4, 0) →* (0, 1, 0, 1, 4*n+4, 0)
  apply stepStar_trans
  · exact r5r1_drain n (4 * n + 4)
  -- Final R5: (0, 1, 0, 1, 4*n+4, 0) →R5 (0, 1, 1, 0, 4*n+4, 0)
  step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 1, 0, 2, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 1, 1, 0, 2 * n + 2, 0⟩) 0
  intro n
  refine ⟨2 * n + 1, ?_⟩
  have h := main_trans n
  rw [show 2 * (2 * n + 1) + 2 = 4 * n + 4 from by ring]
  exact h

end Sz22_2003_unofficial_116
