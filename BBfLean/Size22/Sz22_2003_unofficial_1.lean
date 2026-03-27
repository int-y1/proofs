import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1: [1/105, 10/3, 45/22, 7/2, 363/7]

Vector representation:
```
 0 -1 -1 -1  0
 1 -1  1  0  0
-1  2  1  0 -1
-1  0  0  1  0
 0  1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R3 repeated: transfer a to d
theorem a_to_d : ∀ k, ∀ a d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R4+R0 interleaved drain
theorem drain_chain : ∀ k, ∀ c e, ⟨0, 0, c+k, 2*k+1, e⟩ [fm]⊢* ⟨0, 0, c, 1, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R2/R1/R1 chain
theorem r2r1r1_chain : ∀ k, ∀ a c e, ⟨a+1, 0, c, 0, e+k⟩ [fm]⊢* ⟨a+k+1, 0, c+3*k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: (2*n+1, 0, c+n, 0, 0) ⊢⁺ (2*n+3, 0, c+6*n+7, 0, 0)
theorem main_trans (n c : ℕ) : ⟨2*n+1, 0, c+n, 0, 0⟩ [fm]⊢⁺ ⟨2*n+3, 0, c+6*n+7, 0, 0⟩ := by
  -- Phase 1: (2*n+1, 0, c+n, 0, 0) ⊢* (0, 0, c+n, 2*n+1, 0)
  have h1 : ⟨2*n+1, 0, c+n, 0, 0⟩ [fm]⊢* ⟨0, 0, c+n, 2*n+1, 0⟩ := by
    have := a_to_d (2*n+1) 0 0 (c := c+n)
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2a: (0, 0, c+n, 2*n+1, 0) ⊢* (0, 0, c, 1, 2*n)
  have h2 : ⟨0, 0, c+n, 2*n+1, 0⟩ [fm]⊢* ⟨0, 0, c, 1, 2*n⟩ := by
    have := drain_chain n c 0
    rw [show 0 + 2 * n = 2 * n from by ring] at this; exact this
  -- Phase 2b+3: (0, 0, c, 1, 2*n) ⊢⁺ (2*n+3, 0, c+6*n+7, 0, 0)
  have h3 : ⟨0, 0, c, 1, 2*n⟩ [fm]⊢⁺ ⟨2*n+3, 0, c+6*n+7, 0, 0⟩ := by
    -- R4+R1: 2 steps
    step fm; step fm
    -- Now: (1, 0, c+1, 0, 2*n+2) ⊢* target
    have := r2r1r1_chain (2*n+2) 0 (c+1) 0
    simp only [Nat.zero_add] at this
    apply stepStar_trans this
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1 (stepStar_stepPlus_stepPlus h2 h3)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n c, q = ⟨2*n+1, 0, c+n, 0, 0⟩)
  · intro q ⟨n, c, hq⟩; subst hq
    refine ⟨⟨2*n+3, 0, c+6*n+7, 0, 0⟩, ⟨n+1, c+5*n+6, by ring_nf⟩, main_trans n c⟩
  · exact ⟨0, 0, by unfold c₀; ring_nf⟩
