import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #84: [5/6, 44/35, 91/2, 3/11, 55/13]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  0
-1  0  0  1  0  1
 0  1  0  0 -1  0
 0  0  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_84

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | _ => none

-- Canonical form: (n+1, 0, 0, 0, 2*n, F)
-- Transition: n → n+1, F → F + 2*n

-- Phase 1: R3 repeated: a+k → a, d += k, f += k (when b=0, c=0)
theorem a_to_df : ∀ k, ∀ a d e f, ⟨a+k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d+k, e, f+k⟩ := by
  intro k; induction' k with k h <;> intro a d e f
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Phase 2: R4 repeated: e → 0, b += e (when a=0, c=0)
theorem e_to_b : ∀ k, ∀ b d f, ⟨0, b, 0, d, k, f⟩ [fm]⊢* ⟨0, b+k, 0, d, 0, f⟩ := by
  intro k; induction' k with k h <;> intro b d f
  · exists 0
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 5: Interleaved R1 R1 R2 rounds
-- Each round: 2 R1 steps + 1 R2 step
-- (2, 2k, C, D+k, E, F) →* (2, 0, C+k, D, E+k, F)
theorem r1r1r2_rounds : ∀ k, ∀ C D E F, ⟨2, 2*k, C, D+k, E, F⟩ [fm]⊢* ⟨2, 0, C+k, D, E+k, F⟩ := by
  intro k; induction' k with k h <;> intro C D E F
  · exists 0
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
      show D + (k + 1) = (D + k) + 1 from by ring]
  step fm
  rw [show 2 * k + 1 = 2 * k + 1 from rfl]
  step fm
  rw [show C + 1 + 1 = (C + 1) + 1 from rfl]
  step fm
  apply stepStar_trans (h (C + 1) D (E + 1) F)
  ring_nf; finish

-- Phase 6: Alternating R3 R2 pairs
-- (A+1, 0, k, 0, E, F) →* (A+1+k, 0, 0, 0, E+k, F+k)
theorem r3r2_pairs : ∀ k, ∀ A E F, ⟨A+1, 0, k, 0, E, F⟩ [fm]⊢* ⟨A+1+k, 0, 0, 0, E+k, F+k⟩ := by
  intro k; induction' k with k h <;> intro A E F
  · exists 0
  -- State: (A+1, 0, k+1, 0, E, F)
  -- R1 needs b>=1, no. R2 needs c>=1, d>=1, d=0 no. R3 needs a>=1: yes!
  -- R3: (A, 0, k+1, 1, E, F+1)
  -- Then R2: c=k+1>=1, d=1: (A+2, 0, k, 0, E+1, F+1)
  step fm
  rw [show k + 1 = k + 1 from rfl]
  step fm
  rw [show A + 1 + 1 = (A + 1) + 1 from by ring]
  apply stepStar_trans (h (A + 1) (E + 1) (F + 1))
  ring_nf; finish

-- Main transition: (n+1, 0, 0, 0, 2*n, F) →⁺ (n+2, 0, 0, 0, 2*(n+1), F+2*n)
theorem main_trans (n F : ℕ) : ⟨n+1, 0, 0, 0, 2*n, F⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, 2*(n+1), F+2*n⟩ := by
  -- Phase 1: R3 x (n+1): → (0, 0, 0, n+1, 2n, F+n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, n+1, 2*n, F+n+1⟩)
  · have h := a_to_df (n+1) 0 0 (2*n) F
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 x 2n: → (0, 2n, 0, n+1, 0, F+n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*n, 0, n+1, 0, F+n+1⟩)
  · have h := e_to_b (2*n) 0 (n+1) (F+n+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5: → (0, 2n, 1, n+1, 1, F+n)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*n, 1, n+1, 1, F+n⟩)
  · show fm ⟨0, 2*n, 0, n+1, 0, (F+n)+1⟩ = some ⟨0, 2*n, 1, n+1, 1, F+n⟩
    simp [fm]
  -- Phase 4: R2: → (2, 2n, 0, n, 2, F+n)
  apply stepStar_trans (c₂ := ⟨2, 2*n, 0, n, 2, F+n⟩)
  · apply step_stepStar
    show fm ⟨0, 2*n, 0+1, n+1, 1, F+n⟩ = some ⟨0+2, 2*n, 0, n, 1+1, F+n⟩
    simp [fm]
  -- Phase 5: R1R1R2 x n: → (2, 0, n, 0, n+2, F+n)
  apply stepStar_trans (c₂ := ⟨2, 0, n, 0, 2+n, F+n⟩)
  · have h := r1r1r2_rounds n 0 0 2 (F+n)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 6: R3R2 x n: → (n+2, 0, 0, 0, 2n+2, F+2n)
  have h := r3r2_pairs n 1 (2+n) (F+n)
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, F⟩ ↦ ⟨n+1, 0, 0, 0, 2*n, F⟩) ⟨0, 0⟩
  intro ⟨n, F⟩; exact ⟨⟨n+1, F+2*n⟩, main_trans n F⟩
