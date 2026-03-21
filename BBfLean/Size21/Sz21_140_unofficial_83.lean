import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #83: [5/6, 44/35, 91/2, 3/11, 15/13]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  0
-1  0  0  1  0  1
 0  1  0  0 -1  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_83

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- Phase 1: R3 repeated: (a+k, 0, 0, d, e, f) →* (a, 0, 0, d+k, e, f+k)
theorem a_to_df : ∀ k, ∀ a d f, ⟨a+k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d+k, e, f+k⟩ := by
  intro k; induction' k with k h <;> intro a d f
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2: R4 repeated: (0, b, 0, d, e+k, f) →* (0, b+k, 0, d, e, f)
theorem e_to_b : ∀ k, ∀ b d f, ⟨0, b, 0, d, e+k, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b d f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 4a: R2,R1,R1 rounds
-- Each round: (0, b+2, c+1, d+1, E, F) → (0, b, c+2, d, E+1, F)
-- k rounds: (0, b+2*k, c+1, d+k, E, F) →* (0, b, c+1+k, d, E+k, F)
theorem r2r1r1_rounds : ∀ k, ∀ b c d E F, ⟨0, b+2*k, c+1, d+k, E, F⟩ [fm]⊢* ⟨0, b, c+1+k, d, E+k, F⟩ := by
  intro k; induction' k with k h <;> intro b c d E F
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm  -- R2: needs c+1≥1, d+k+1≥1
  step fm  -- R1: needs a≥1 (a=2), b≥1 (b+2*k+2≥2)
  step fm  -- R1: needs a≥1 (a=1), b≥1
  apply stepStar_trans (h _ _ _ _ _)
  ring_nf; finish

-- Phase 5: R3,R2 pairs
-- Each pair: (a+1, 0, c+1, 0, E, F) → R3 → (a, 0, c+1, 1, E, F+1) → R2 → (a+2, 0, c, 0, E+1, F+1)
-- k pairs: (a+1, 0, k, 0, E, F) →* (a+1+k, 0, 0, 0, E+k, F+k)
theorem r3r2_pairs : ∀ k, ∀ a E F, ⟨a+1, 0, k, 0, E, F⟩ [fm]⊢* ⟨a+1+k, 0, 0, 0, E+k, F+k⟩ := by
  intro k; induction' k with k h <;> intro a E F
  · exists 0
  rw [show (k : ℕ) + 1 = k + 1 from rfl]
  step fm  -- R3: a+1≥1, b=0 so R1 doesn't match; c=k+1 but d=0 so R2 doesn't match
  step fm  -- R2: c=k+1≥1, d=1≥1
  apply stepStar_trans (h (a + 1) (E + 1) (F + 1))
  ring_nf; finish

-- Main transition: (n+1, 0, 0, 0, 2*n, n*n) →⁺ (n+2, 0, 0, 0, 2*(n+1), (n+1)*(n+1))
theorem main_trans : ⟨n+1, 0, 0, 0, 2*n, n*n⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, 2*n+2, (n+1)*(n+1)⟩ := by
  -- Phase 1: R3*(n+1): → (0, 0, 0, n+1, 2n, n²+n+1)
  apply step_stepStar_stepPlus
  · -- First R3 step
    show fm ⟨n + 1, 0, 0, 0, 2 * n, n * n⟩ = some ⟨n, 0, 0, 1, 2 * n, n * n + 1⟩
    simp [fm]
  -- Now at (n, 0, 0, 1, 2n, n²+1), need to reach (0, 0, 0, n+1, 2n, n²+n+1) via n more R3 steps
  apply stepStar_trans (c₂ := ⟨0, 0, 0, n+1, 2*n, n*n+n+1⟩)
  · have h := @a_to_df (2*n) n 0 1 (n*n+1)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  -- Phase 2: R4*(2n): → (0, 2n, 0, n+1, 0, n²+n+1)
  apply stepStar_trans (c₂ := ⟨0, 2*n, 0, n+1, 0, n*n+n+1⟩)
  · have h := @e_to_b 0 (2*n) 0 (n+1) (n*n+n+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5: → (0, 2n+1, 1, n+1, 0, n²+n)
  apply stepStar_trans (c₂ := ⟨0, 2*n+1, 1, n+1, 0, n*n+n⟩)
  · rw [show n*n+n+1 = (n*n+n) + 1 from by ring]
    step fm
    finish
  -- Phase 4a: R2R1R1 rounds * n: → (0, 1, n+1, 1, n, n²+n)
  apply stepStar_trans (c₂ := ⟨0, 1, n+1, 1, n, n*n+n⟩)
  · rw [show 2*n+1 = 1+2*n from by ring,
        show (n : ℕ)+1 = 1+n from by ring]
    have h := @r2r1r1_rounds n 1 0 1 0 (n*n+n)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  -- Phase 4b: R2, R1: → (1, 0, n+1, 0, n+1, n²+n)
  apply stepStar_trans (c₂ := ⟨1, 0, n+1, 0, n+1, n*n+n⟩)
  · rw [show (n : ℕ)+1 = n + 1 from rfl]
    step fm  -- R2
    step fm  -- R1
    ring_nf; finish
  -- Phase 5: R3R2 pairs * (n+1): → (n+2, 0, 0, 0, 2n+2, n²+2n+1)
  have h := @r3r2_pairs (n+1) 0 (n+1) (n*n+n)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1, 0, 0, 0, 0, 0) is already the canonical form with n=0
  -- C(n) = (n+1, 0, 0, 0, 2*n, n*n)
  -- C(0) = (1, 0, 0, 0, 0, 0) = c₀
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, 0, 2*n, n*n⟩) 0
  intro n; exact ⟨n+1, main_trans⟩
