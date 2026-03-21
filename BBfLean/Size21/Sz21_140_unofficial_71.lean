import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #71: [4/15, 33/14, 5/2, 7/11, 66/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 1  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_71

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | _ => none

-- R3 repeated: a → c
theorem a_to_c : ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
  have many_step : ∀ k a c, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
    intro k; induction' k with k h <;> intro a c
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a c

-- R4 repeated: e → d
theorem e_to_d : ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  have many_step : ∀ k d e, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k d e

-- R1/R2 chain: k rounds
theorem r1r2_chain : ⟨a, 1, c+k, d+k, e⟩ [fm]⊢* ⟨a+k, 1, c, d, e+k⟩ := by
  have many_step : ∀ k a c d e, ⟨a, 1, c+k, d+k, e⟩ [fm]⊢* ⟨a+k, 1, c, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro a c d e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (h _ _ _ _)
    ring_nf; finish
  exact many_step k a c d e

-- Main transition: (n+1, 0, 0, 0, n) → (n+2, 0, 0, 0, n+1)
theorem main_trans : ⟨n+1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, n+1⟩ := by
  -- Phase 1: R3 × (n+1): a → c
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, 0, n⟩)
  · have h := @a_to_c 0 (n+1) 0 n
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 × n: e → d
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, n, 0⟩)
  · have h := @e_to_d (n+1) 0 0 n
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5
  apply step_stepStar_stepPlus (c₂ := ⟨1, 1, n, n, 1⟩)
  · show fm ⟨0, 0, n + 1, n, 0⟩ = some ⟨1, 1, n, n, 1⟩; simp [fm]
  -- Phase 4: R1/R2 chain × n
  apply stepStar_trans (c₂ := ⟨n+1, 1, 0, 0, n+1⟩)
  · show ⟨1, 1, n, n, 1⟩ [fm]⊢* ⟨n+1, 1, 0, 0, n+1⟩
    have h := @r1r2_chain 1 0 n 0 1
    simp only [Nat.zero_add] at h
    rwa [show (1 : ℕ) + n = n + 1 from by omega] at h
  -- Phase 5: R3 then R1
  step fm
  step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, 0, n⟩) 0
  intro n; exact ⟨n+1, main_trans⟩
