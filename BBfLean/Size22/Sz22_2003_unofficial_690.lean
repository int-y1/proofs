import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #690: [35/6, 4/55, 11/2, 3/7, 490/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 1  0  1  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_690

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d+2, e⟩
  | _ => none

-- R3 chain: drain a into e
theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1))
    ring_nf; finish

-- R4 chain: drain d into b
theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R1/R2/R1 cycle: k rounds consuming b and e, building c and d
theorem r1r2r1_cycle : ∀ k, ∀ c d, ⟨1, 2 * k, c, d, k⟩ [fm]⊢* ⟨1, 0, c + k, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring,
        show k + 1 = k + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2))
    ring_nf; finish

-- R2/R3 interleave: drain c, building a
theorem r2r3_interleave : ∀ k, ∀ a d, ⟨a, 0, k + 1, d, 1⟩ [fm]⊢* ⟨a + k + 2, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; finish
  · rw [show (k : ℕ) + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) d)
    ring_nf; finish

-- Main transition: canonical state to next canonical state
theorem main_transition (k : ℕ) : ⟨0, 2 * k, 0, 0, k + 1⟩ [fm]⊢⁺ ⟨0, 2 * k + 2, 0, 0, k + 2⟩ := by
  -- Phase 1: R5
  rw [show k + 1 = k + 1 from rfl]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * k, 0, 0, k + 1⟩ = some ⟨1, 2 * k, 1, 2, k⟩
    rcases k with _ | k
    · simp [fm]
    · simp [fm]
  -- Phase 2: R1/R2/R1 cycle
  apply stepStar_trans (r1r2r1_cycle k 1 2)
  -- Now at (1, 0, k+1, 2k+2, 0)
  -- Phase 3: R3 step
  rw [show 1 + k = k + 1 from by ring, show 2 + 2 * k = 2 * k + 2 from by ring]
  step fm
  -- Now at (0, 0, k+1, 2k+2, 1)
  -- Phase 4: R2/R3 interleave
  apply stepStar_trans (r2r3_interleave k 0 (2 * k + 2))
  -- Now at (k+2, 0, 0, 2k+2, 0)
  rw [show 0 + k + 2 = 0 + (k + 2) from by ring]
  -- Phase 5: R3 chain
  apply stepStar_trans (r3_chain (k + 2) 0 (2 * k + 2) 0)
  -- Now at (0, 0, 0, 2k+2, k+2)
  rw [show 0 + (k + 2) = k + 2 from by ring, show 2 * k + 2 = 0 + (2 * k + 2) from by ring]
  -- Phase 6: R4 chain
  apply stepStar_trans (r4_chain (2 * k + 2) 0 0 (k + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 2 * k, 0, 0, k + 1⟩) 1
  intro k; exists k + 1
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
  exact main_transition k
