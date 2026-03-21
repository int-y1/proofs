import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #129: [9/10, 55/21, 2/3, 7/11, 99/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_129

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- R2/R1 chain: each pair (a+1, b+1, 0, d+1, e) →→ (a, b+2, 0, d, e+1)
-- After k pairs: (a+k, b+1, 0, d+k, e) →* (a, b+k+1, 0, d, e+k)
theorem r2r1_chain : ∀ k, ∀ a b d e, ⟨a+k, b+1, 0, d+k, e⟩ [fm]⊢* ⟨a, b+k+1, 0, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  -- R2: (a+k+1, b+1, 0, d+k+1, e) → (a+k+1, b, 1, d+k, e+1)
  step fm
  -- R1: (a+k+1, b, 1, d+k, e+1) → (a+k, b+2, 0, d+k, e+1)
  step fm
  have h2 := h a (b + 1) d (e + 1)
  rw [show b + 1 + 1 = b + 2 from by ring] at h2
  refine stepStar_trans h2 ?_
  ring_nf; finish

-- R3 repeated: b → a (when c=0, d=0)
theorem b_to_a : ∀ k, ∀ a b e, ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+k, b, 0, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a b e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ b _)
  ring_nf; finish

-- R4 repeated: e → d (when b=0, c=0)
theorem e_to_d : ∀ k, ∀ a d e, ⟨a, 0, 0, d, e+k⟩ [fm]⊢* ⟨a, 0, 0, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h a _ e)
  ring_nf; finish

-- Main transition: (n+1, 0, 0, n, 0) →⁺ (n+2, 0, 0, n+1, 0)
theorem main_trans : ⟨n+1, 0, 0, n, 0⟩ [fm]⊢⁺ ⟨n+2, 0, 0, n+1, 0⟩ := by
  -- Phase 1: R5 step (gives stepPlus)
  -- (n+1, 0, 0, n, 0) → (n, 2, 0, n, 1)
  apply step_stepStar_stepPlus (c₂ := ⟨n, 2, 0, n, 1⟩)
  · show fm ⟨n + 1, 0, 0, n, 0⟩ = some ⟨n, 2, 0, n, 1⟩; simp [fm]
  -- Phase 2: R2/R1 chain (n pairs)
  -- (n, 2, 0, n, 1) = (0+n, 1+1, 0, 0+n, 1) →* (0, 1+n+1, 0, 0, 1+n) = (0, n+2, 0, 0, n+1)
  apply stepStar_trans (c₂ := ⟨0, n+2, 0, 0, n+1⟩)
  · have h := r2r1_chain n 0 1 0 1
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  -- Phase 3: R3 chain (n+2 times)
  -- (0, n+2, 0, 0, n+1) →* (n+2, 0, 0, 0, n+1)
  apply stepStar_trans (c₂ := ⟨n+2, 0, 0, 0, n+1⟩)
  · have h := b_to_a (n+2) 0 0 (n+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 4: R4 chain (n+1 times)
  -- (n+2, 0, 0, 0, n+1) →* (n+2, 0, 0, n+1, 0)
  · have h := e_to_d (n+1) (n+2) 0 0
    simp only [Nat.zero_add] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, n, 0⟩) 0
  intro n; exact ⟨n+1, main_trans⟩
