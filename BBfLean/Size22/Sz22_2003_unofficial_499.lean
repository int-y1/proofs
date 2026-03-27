import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #499: [28/15, 3/22, 25/2, 121/7, 33/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  2
 0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_499

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r3_chain : ∀ k : ℕ, ∀ c d,
    ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · simp; exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

theorem r4_chain : ∀ k : ℕ, ∀ c e,
    ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · simp; exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

theorem r1r2_chain : ∀ k : ℕ, ∀ a c d e,
    ⟨a, 1, c + k, d, e + k⟩ [fm]⊢* ⟨a + k, 1, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · simp; exists 0
  rw [show c + (k + 1) = (c + 1) + k from by ring,
      show e + (k + 1) = (e + 1) + k from by ring]
  apply stepStar_trans (ih _ _ _ _)
  step fm; step fm
  ring_nf; finish

theorem r2_drain : ∀ k : ℕ, ∀ a b d,
    ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · simp; exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

theorem tail : ∀ B : ℕ, ∀ A D,
    ⟨A + 1, B, 0, D, 0⟩ [fm]⊢* ⟨0, 0, 2 * A + 3 * B + 2, D + B, 0⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih
  rcases B with _ | _ | B
  · intro A D
    convert r3_chain (A + 1) 0 D using 2
    all_goals ring_nf
  · intro A D
    step fm; step fm; step fm; step fm
    apply stepStar_trans (r3_chain A _ _)
    ring_nf; finish
  · intro A D
    step fm; step fm; step fm
    apply stepStar_trans (ih B (by omega) (A + 3) (D + 2))
    ring_nf; finish

-- Phase after R1-R2 chain: from (a+b+2, 0, 0, a+b+1, b+1) to final state
theorem phase_after_chain : ∀ a b : ℕ,
    ⟨a + b + 2, 0, 0, a + b + 1, b + 1⟩ [fm]⊢*
    ⟨0, 0, 2 * a + 3 * b + 5, 0, 2 * a + 4 * b + 4⟩ := by
  intro a b
  -- R2 drain (b+1 steps)
  apply stepStar_trans
  · rw [show a + b + 2 = (a + 1) + (b + 1) from by ring]
    exact r2_drain (b + 1) (a + 1) 0 (a + b + 1)
  -- Tail
  apply stepStar_trans
  · rw [show 0 + (b + 1) = b + 1 from by ring]
    exact tail (b + 1) a (a + b + 1)
  -- R4 chain
  apply stepStar_trans
  · rw [show a + b + 1 + (b + 1) = a + 2 * b + 2 from by ring]
    exact r4_chain (a + 2 * b + 2) (2 * a + 3 * b + 5) 0
  ring_nf; finish

-- Full transition with ⊢⁺
theorem full_trans : ∀ a b : ℕ,
    ⟨0, 0, a + b + 2, 0, a + 2 * b⟩ [fm]⊢⁺
    ⟨0, 0, 2 * a + 3 * b + 5, 0, 2 * a + 4 * b + 4⟩ := by
  intro a b
  -- R5 step gives the ⊢⁺
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (a + b + 1) + 1, 0, a + 2 * b⟩ = some ⟨0, 1, a + b + 1, 0, a + 2 * b + 1⟩
    simp [fm]
  -- R1-R2 chain (a+b rounds): (0, 1, a+b+1, 0, a+2b+1) → (a+b, 1, 1, a+b, b+1)
  apply stepStar_trans
  · rw [show a + b + 1 = 1 + (a + b) from by ring,
        show a + 2 * b + 1 = (b + 1) + (a + b) from by ring]
    exact r1r2_chain (a + b) 0 1 0 (b + 1)
  -- Final R1: (a+b, 1, 1, a+b, b+1) → (a+b+2, 0, 0, a+b+1, b+1)
  apply stepStar_trans (c₂ := ⟨a + b + 2, 0, 0, a + b + 1, b + 1⟩)
  · simp only [Nat.zero_add]; step fm; ring_nf; finish
  -- Remaining phases
  exact phase_after_chain a b

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, b⟩ ↦ ⟨0, 0, a + b + 2, 0, a + 2 * b⟩) ⟨0, 0⟩
  intro ⟨a, b⟩
  refine ⟨⟨2 * a + 2 * b + 2, b + 1⟩, ?_⟩
  simp only []
  convert full_trans a b using 2
  ring_nf

end Sz22_2003_unofficial_499
