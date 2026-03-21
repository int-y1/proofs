import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #128: [9/10, 55/21, 2/3, 7/11, 63/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_128

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R2/R1 chain: k rounds of (R2, R1)
-- Each round: (A, B, 0, D, E) -> (A-1, B+1, 0, D-1, E+1)
theorem r2r1_chain : ∀ k, ∀ a b d e, ⟨a+k, b+1, 0, d+k, e⟩ [fm]⊢* ⟨a, b+1+k, 0, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm  -- R2: (a+k+1, b+1, 0, d+k+1, e) -> (a+k+1, b, 1, d+k, e+1)
  step fm  -- R1: (a+k+1, b, 1, d+k, e+1) -> (a+k, b+2, 0, d+k, e+1)
  rw [show b + 2 = (b + 1) + 1 from by ring]
  apply stepStar_trans (ih a (b + 1) d (e + 1))
  ring_nf; finish

-- R3 repeated: b → a (when c=0, d=0)
theorem b_to_a : ∀ k, ∀ a b e, ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show b + (k + 1) = b + k + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 repeated: e → d (when b=0, c=0)
theorem e_to_d : ∀ k, ∀ a d e, ⟨a, 0, 0, d, e+k⟩ [fm]⊢* ⟨a, 0, 0, d+k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = e + k + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Main transition: (d+1, 0, 0, d, 0) ⊢⁺ (d+2, 0, 0, d+1, 0)
theorem main_trans : ⟨d+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨d+2, 0, 0, d+1, 0⟩ := by
  -- Phase 1: R5 step
  apply step_stepStar_stepPlus (c₂ := ⟨d, 2, 0, d+1, 0⟩)
  · show fm ⟨d + 1, 0, 0, d, 0⟩ = some ⟨d, 2, 0, d + 1, 0⟩
    simp [fm]
  -- Phase 2: R2/R1 chain, d rounds
  -- (d, 2, 0, d+1, 0): match with (a+k, b+1, 0, D+k, e) where a=0, k=d, b=1, D=1, e=0
  -- Result: (0, 1+1+d, 0, 1, 0+d) = (0, d+2, 0, 1, d)
  apply stepStar_trans (c₂ := ⟨0, d+2, 0, 1, d⟩)
  · have h := r2r1_chain d 0 1 1 0
    simp only [Nat.zero_add] at h
    convert h using 2
    all_goals ring_nf
  -- Phase 3: R2 step
  -- (0, d+2, 0, 1, d) ->R2 (0, d+1, 1, 0, d+1)
  apply stepStar_trans (c₂ := ⟨0, d+1, 1, 0, d+1⟩)
  · rw [show d + 2 = (d + 1) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm; finish
  -- Phase 4: R3 then R1
  -- (0, d+1, 1, 0, d+1) ->R3 (1, d, 1, 0, d+1) ->R1 (0, d+2, 0, 0, d+1)
  apply stepStar_trans (c₂ := ⟨0, d+2, 0, 0, d+1⟩)
  · rw [show d + 1 = d + 1 from rfl]
    step fm  -- R3
    step fm  -- R1
    finish
  -- Phase 5: R3 chain (d+2 times): b → a
  -- (0, d+2, 0, 0, d+1) ->* (d+2, 0, 0, 0, d+1)
  apply stepStar_trans (c₂ := ⟨d+2, 0, 0, 0, d+1⟩)
  · have h := b_to_a (d+2) 0 0 (d+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 6: R4 chain (d+1 times): e → d
  -- (d+2, 0, 0, 0, d+1) ->* (d+2, 0, 0, d+1, 0)
  have h := e_to_d (d+1) (d+2) 0 0
  simp only [Nat.zero_add] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨d+1, 0, 0, d, 0⟩) 1
  intro d; exact ⟨d+1, main_trans⟩

end Sz21_140_unofficial_128
