import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #8: [1/105, 4/3, 15/22, 35/2, 363/5]

Vector representation:
```
 0 -1 -1 -1  0
 2 -1  0  0  0
-1  1  1  0 -1
-1  0  1  1  0
 0  1 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_8

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- Phase 1: R3/R2 interleaved chain
-- Each pair: (a+1, 0, c, 0, e+1) → (a+2, 0, c+1, 0, e)
theorem r3r2_chain : ∀ k, ∀ a c, ⟨a+1, 0, c, 0, k+1⟩ [fm]⊢* ⟨a+k+2, 0, c+k+1, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · step fm; step fm; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Phase 2: R4 chain
-- Each step: (a+1, 0, c, d, 0) → (a, 0, c+1, d+1, 0)
theorem r4_chain : ∀ k, ∀ c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c+k, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Phase 3: R5/R1 drain chain
-- Each pair: (0, 0, c+2, d+1, f) → (0, 0, c, d, f+2)
theorem r5r1_chain : ∀ k, ∀ f, ⟨0, 0, 2*k+1, k+1, f⟩ [fm]⊢* ⟨0, 0, 1, 1, f+2*k⟩ := by
  intro k; induction' k with k ih <;> intro f
  · ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
         show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- Phase 4: Final 4 steps from (0, 0, 1, 1, 2e+2) to (1, 0, 0, 0, 2e+1)
theorem final_steps : ⟨0, 0, 1, 1, f⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, f + 1⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Main transition for e ≥ 1: (1, 0, 0, 0, e+1) ⊢⁺ (1, 0, 0, 0, 2*e+3)
theorem main_trans : ⟨1, 0, 0, 0, e+1⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2*e+3⟩ := by
  -- Phase 1: R3/R2 chain: (1, 0, 0, 0, e+1) →* (e+2, 0, e+1, 0, 0)
  apply stepStar_stepPlus_stepPlus (r3r2_chain e 0 0)
  simp only [Nat.zero_add]
  -- Phase 2: R4 chain: (e+2, 0, e+1, 0, 0) →* (0, 0, 2*e+3, e+2, 0)
  apply stepStar_stepPlus_stepPlus (r4_chain (e+2) (e+1) 0)
  simp only [Nat.zero_add]
  -- Phase 3: R5/R1 drain: (0, 0, 2*e+3, e+2, 0) →* (0, 0, 1, 1, 2*(e+1))
  rw [show e + 2 = (e + 1) + 1 from by ring,
      show e + 1 + ((e + 1) + 1) = 2 * (e + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain (e+1) 0)
  simp only [Nat.zero_add]
  -- Phase 4: Final steps: (0, 0, 1, 1, 2*(e+1)) →⁺ (1, 0, 0, 0, 2*e+3)
  apply stepPlus_stepStar_stepPlus final_steps
  ring_nf; finish

-- Bootstrap transition for e=0: (1, 0, 0, 0, 0) ⊢⁺ (1, 0, 0, 0, 1)
theorem bootstrap : ⟨1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 1⟩ := by
  execute fm 5

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨1, 0, 0, 0, e⟩) 0
  intro e
  rcases e with _ | e
  · exact ⟨1, bootstrap⟩
  · exact ⟨2*e+3, main_trans⟩

end Sz22_2003_unofficial_8
