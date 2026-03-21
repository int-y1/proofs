import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #63: [4/15, 33/14, 25/2, 7/11, 21/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_63

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R1/R2 chain: (j, 1, X+D, D, j) →* (j+D, 1, X, 0, j+D)
theorem r1r2_chain : ∀ D, ∀ j X, ⟨j, 1, X + D, D, j⟩ [fm]⊢* ⟨j + D, 1, X, 0, j + D⟩ := by
  intro D; induction' D with D ih <;> intro j X
  · exists 0
  rw [show X + (D + 1) = (X + D) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (ih (j + 1) X)
  ring_nf; finish

-- R3 repeated: a → c
theorem r3_chain : ∀ k, ∀ a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a _ e)
  ring_nf; finish

-- R4 repeated: e → d
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show e + (k + 1) = e + k + 1 from by ring]
  step fm
  apply stepStar_trans (ih c _ e)
  ring_nf; finish

-- Main transition: (0, 0, c, d, 0) →+ (0, 0, c+d+3, d+1, 0) when c >= d+3
theorem main_trans (c d : ℕ) (hc : c ≥ d + 3) : ⟨0, 0, c, d, 0⟩ [fm]⊢⁺ ⟨0, 0, c + d + 3, d + 1, 0⟩ := by
  obtain ⟨C, hC⟩ : ∃ C, c = C + (d + 3) := ⟨c - (d + 3), by omega⟩
  subst hC
  -- Phase 1: R5
  rw [show C + (d + 3) = (C + (d + 2)) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (C + (d + 2)) + 1, d, 0⟩ = some ⟨0, 1, C + (d + 2), d + 1, 0⟩
    simp [fm]
  -- Phase 2: R1/R2 chain
  apply stepStar_trans (c₂ := ⟨d + 1, 1, C + 1, 0, d + 1⟩)
  · rw [show C + (d + 2) = (C + 1) + (d + 1) from by ring]
    have h := r1r2_chain (d + 1) 0 (C + 1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: one more R1
  apply stepStar_trans (c₂ := ⟨d + 3, 0, C, 0, d + 1⟩)
  · rw [show C + 1 = C + 1 from rfl]
    have : fm ⟨d + 1, 1, C + 1, 0, d + 1⟩ = some ⟨d + 3, 0, C, 0, d + 1⟩ := by
      show fm ⟨d + 1, 0 + 1, C + 1, 0, d + 1⟩ = some ⟨d + 1 + 2, 0, C, 0, d + 1⟩
      simp [fm]
    exact step_stepStar this
  -- Phase 4: R3 chain
  apply stepStar_trans (c₂ := ⟨0, 0, C + 2 * (d + 3), 0, d + 1⟩)
  · have h3 := r3_chain (d + 3) 0 C (d + 1)
    simp only [Nat.zero_add] at h3; exact h3
  -- Phase 5: R4 chain
  have h4 := r4_chain (d + 1) (C + 2 * (d + 3)) 0 0
  simp only [Nat.zero_add] at h4
  refine stepStar_trans h4 ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 1, 0⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c, d, 0⟩ ∧ c ≥ d + 3)
  · intro q ⟨c, d, hq, hc⟩; subst hq
    exact ⟨⟨0, 0, c + d + 3, d + 1, 0⟩,
      ⟨c + d + 3, d + 1, rfl, by omega⟩,
      main_trans c d hc⟩
  · exact ⟨5, 1, rfl, by omega⟩

end Sz21_140_unofficial_63
