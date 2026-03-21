import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #23: [28/15, 3/22, 5/2, 11/7, 42/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  1  0  0
 0  0  0 -1  1
 1  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_23

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d+1, e⟩
  | _ => none

-- Phase 1: R3 repeated: a → c
theorem a_to_c : ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  have many_step : ∀ k, ∀ a c, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
    intro k; induction' k with k h <;> intro a c
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a c

-- Phase 2: R4 repeated: d → e
theorem d_to_e : ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  have many_step : ∀ k, ∀ d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k d e

-- Phase 3b: (R2, R1) chain
theorem r2r1_chain : ∀ k, ∀ a c d e, ⟨a+1, 0, c+k, d, e+k⟩ [fm]⊢* ⟨a+1+k, 0, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Phase 4: R2 repeated: a,e → b
theorem a_to_b : ∀ k, ∀ a b d, ⟨a+k, b, 0, d, k⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 5: (R3, R1) chain
theorem r3r1_chain : ∀ k, ∀ a d, ⟨a+1, k, 0, d, 0⟩ [fm]⊢* ⟨a+1+k, 0, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  step fm
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Combined phase 3: (0, 0, n+2, 0, 2n+2) →* (n+3, 0, 0, n+2, n+2)
theorem phase3 (n : ℕ) : ⟨0, 0, n+2, 0, 2*n+2⟩ [fm]⊢* ⟨n+3, 0, 0, n+2, n+2⟩ := by
  -- R5: (0, 0, (n+1)+1, 0, 2n+2) → (1, 1, n+1, 1, 2n+2)
  apply stepStar_trans (c₂ := ⟨1, 1, n+1, 1, 2*n+2⟩)
  · have : fm ⟨0, 0, (n+1)+1, 0, 2*n+2⟩ = some ⟨1, 1, n+1, 1, 2*n+2⟩ := by simp [fm]
    exact step_stepStar this
  -- R1: (1, 0+1, n+1, 1, 2n+2) → (3, 0, n, 2, 2n+2)
  apply stepStar_trans (c₂ := ⟨3, 0, n, 2, 2*n+2⟩)
  · have : fm ⟨1, 0+1, n+1, 1, 2*n+2⟩ = some ⟨3, 0, n, 2, 2*n+2⟩ := by simp [fm]
    exact step_stepStar this
  -- (R2, R1) x n
  have h := r2r1_chain n 2 0 2 (n+2)
  convert h using 1; ring_nf

-- Combined phase 4+5: (n+3, 0, 0, n+2, n+2) →* (n+3, 0, 0, 2n+4, 0)
theorem phase45 (n : ℕ) : ⟨n+3, 0, 0, n+2, n+2⟩ [fm]⊢* ⟨n+3, 0, 0, 2*n+4, 0⟩ := by
  -- Phase 4: R2 x(n+2): (n+3, 0, 0, n+2, n+2) →* (1, n+2, 0, n+2, 0)
  apply stepStar_trans (c₂ := ⟨1, n+2, 0, n+2, 0⟩)
  · have h := a_to_b (n+2) 1 0 (n+2)
    convert h using 1; ring_nf
  -- Phase 5: r3r1_chain
  have h := r3r1_chain (n+2) 0 (n+2)
  convert h using 1; ring_nf

-- Main transition
theorem main_trans (n : ℕ) : ⟨n+2, 0, 0, 2*n+2, 0⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 2*n+4, 0⟩ := by
  -- Phase 1: (n+2, 0, 0, 2n+2, 0) →* (0, 0, n+2, 2n+2, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+2, 2*n+2, 0⟩)
  · have h := @a_to_c 0 (n+2) 0 (2*n+2)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: →* (0, 0, n+2, 0, 2n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+2, 0, 2*n+2⟩)
  · have h := @d_to_e (n+2) 0 (2*n+2) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: →⁺ via R5 step then rest
  -- R5 gives the first step (stepPlus)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 1, n+1, 1, 2*n+2⟩)
  · show fm ⟨0, 0, (n + 1) + 1, 0, 2 * n + 2⟩ = some ⟨1, 1, n + 1, 1, 2 * n + 2⟩
    simp [fm]
  -- R1 step
  apply stepStar_trans (c₂ := ⟨3, 0, n, 2, 2*n+2⟩)
  · have : fm ⟨1, 0+1, n+1, 1, 2*n+2⟩ = some ⟨3, 0, n, 2, 2*n+2⟩ := by simp [fm]
    exact step_stepStar this
  -- Phase 3b: →* (n+3, 0, 0, n+2, n+2)
  apply stepStar_trans (c₂ := ⟨n+3, 0, 0, n+2, n+2⟩)
  · have h := r2r1_chain n 2 0 2 (n+2)
    convert h using 1; ring_nf
  -- Phase 4+5: →* (n+3, 0, 0, 2n+4, 0)
  exact phase45 n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+2, 0, 0, 2*n+2, 0⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩
