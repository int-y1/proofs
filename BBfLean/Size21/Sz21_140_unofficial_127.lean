import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #127: [9/10, 55/21, 2/3, 7/11, 165/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_127

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

-- R3 repeated: b → a
theorem b_to_a : ∀ k, ∀ a b, ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+k, b, 0, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R4 repeated: e → d
theorem e_to_d : ∀ k, ∀ d e, ⟨a, 0, 0, d, e+k⟩ [fm]⊢* ⟨a, 0, 0, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1/R2 interleaved chain
theorem r1r2_pair : ∀ k, ∀ a b, ⟨a+k, b, 1, a+k, b⟩ [fm]⊢* ⟨a, b+k, 1, a, b+k⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  have hR2 : ⟨a + k, b + 2, 0, (a + k) + 1, b⟩ [fm]⊢ ⟨a + k, b + 1, 1, a + k, b + 1⟩ := by
    show fm ⟨a + k, (b + 1) + 1, 0, (a + k) + 1, b⟩ = some ⟨a + k, b + 1, 1, a + k, b + 1⟩
    simp [fm]
  apply stepStar_trans (step_stepStar hR2)
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Main transition: (n+1, 0, 0, n, 0) →⁺ (n+2, 0, 0, n+1, 0)
theorem main_trans : ⟨n+1, 0, 0, n, 0⟩ [fm]⊢⁺ ⟨n+2, 0, 0, n+1, 0⟩ := by
  -- Phase 1: R5
  apply step_stepStar_stepPlus (c₂ := ⟨n, 1, 1, n, 1⟩)
  · show fm ⟨n + 1, 0, 0, n, 0⟩ = some ⟨n, 1, 1, n, 1⟩
    simp [fm]
  -- Phase 2: R1/R2 chain
  apply stepStar_trans (c₂ := ⟨0, n+1, 1, 0, n+1⟩)
  · have h := r1r2_pair n 0 1
    simp only [Nat.zero_add] at h
    rw [show (1 : ℕ) + n = n + 1 from by ring] at h; exact h
  -- Phase 3: R3 then R1
  apply stepStar_trans (c₂ := ⟨0, n+2, 0, 0, n+1⟩)
  · rw [show n + 1 = n + 1 from rfl]
    step fm
    step fm
    finish
  -- Phase 4: b → a
  apply stepStar_trans (c₂ := ⟨n+2, 0, 0, 0, n+1⟩)
  · have h := b_to_a (n+2) 0 0 (e := n+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 5: e → d
  · have h := e_to_d (n+1) 0 0 (a := n+2)
    simp only [Nat.zero_add] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, n, 0⟩) 0
  intro n; exact ⟨n+1, main_trans⟩
