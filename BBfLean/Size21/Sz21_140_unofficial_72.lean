import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #72: [4/15, 33/14, 65/2, 7/11, 14/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_72

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

-- Phase 1: R3 repeated: a → c,f (when b=0, d=0)
-- (a+k, 0, c, 0, e, f) →* (a, 0, c+k, 0, e, f+k)
theorem a_to_cf : ⟨a+k, 0, c, 0, e, f⟩ [fm]⊢* ⟨a, 0, c+k, 0, e, f+k⟩ := by
  have many_step : ∀ k a c f, ⟨a+k, 0, c, 0, e, f⟩ [fm]⊢* ⟨a, 0, c+k, 0, e, f+k⟩ := by
    intro k; induction' k with k h <;> intro a c f
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k a c f

-- Phase 2: R4 repeated: e → d (when a=0, b=0)
-- (0, 0, c, d, e+k, f) →* (0, 0, c, d+k, e, f)
theorem e_to_d : ⟨0, 0, c, d, e+k, f⟩ [fm]⊢* ⟨0, 0, c, d+k, e, f⟩ := by
  have many_step : ∀ k d e, ⟨0, 0, c, d, e+k, f⟩ [fm]⊢* ⟨0, 0, c, d+k, e, f⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k d e

-- Phase 3: R5 one step
-- (0, 0, c, d, 0, f+1) → (1, 0, c, d+1, 0, f)

-- Phase 4: R2,R1 chain
-- From (k+1, 0, c+1, c+1, k, F) we do R2 then R1 to get (k+2, 0, c, c, k+1, F)
-- Repeated: from (1, 0, n+1, n+1, 0, F) to (n+2, 0, 0, 0, n+1, F)
theorem r2r1_chain : ∀ j, ∀ k c, ⟨k+1, 0, c+j, c+j, k, F⟩ [fm]⊢* ⟨k+j+1, 0, c, c, k+j, F⟩ := by
  intro j; induction' j with j h <;> intro k c
  · exists 0
  -- Current state: (k+1, 0, c+(j+1), c+(j+1), k, F)
  -- = (k+1, 0, (c+j)+1, (c+j)+1, k, F) with d = c+j+1 ≥ 1
  -- R2: a=k+1≥1, d=c+j+1≥1 → (k, 1, (c+j)+1, c+j, k+1, F)
  -- R1: b=1≥1, c=(c+j)+1≥1 → (k+2, 0, c+j, c+j, k+1, F)
  rw [show c + (j + 1) = (c + j) + 1 from by ring]
  -- State: (k+1, 0, (c+j)+1, (c+j)+1, k, F)
  -- R2 step
  apply stepStar_trans (c₂ := ⟨k, 1, (c + j) + 1, c + j, k + 1, F⟩)
  · have : fm ⟨k + 1, 0, (c + j) + 1, (c + j) + 1, k, F⟩ = some ⟨k, 1, (c + j) + 1, c + j, k + 1, F⟩ := by
      show fm ⟨k + 1, 0, (c + j) + 1, (c + j) + 1, k, F⟩ = some ⟨k, 0 + 1, (c + j) + 1, c + j, k + 1, F⟩
      simp [fm]
    exact step_stepStar this
  -- R1 step: b=1, c=(c+j)+1
  apply stepStar_trans (c₂ := ⟨k + 2, 0, c + j, c + j, k + 1, F⟩)
  · have : fm ⟨k, 1, (c + j) + 1, c + j, k + 1, F⟩ = some ⟨k + 2, 0, c + j, c + j, k + 1, F⟩ := by
      show fm ⟨k, 0 + 1, (c + j) + 1, c + j, k + 1, F⟩ = some ⟨k + 2, 0, c + j, c + j, k + 1, F⟩
      simp [fm]
    exact step_stepStar this
  -- Now apply IH
  have h2 := h (k + 1) c
  rw [show k + 1 + 1 = k + 2 from by ring] at h2
  refine stepStar_trans h2 ?_
  ring_nf; finish

-- Main transition: (n+1, 0, 0, 0, n, n*(n-1)/2) ⊢⁺ (n+2, 0, 0, 0, n+1, n*(n+1)/2)
-- We parameterize by n and F where F = n*(n-1)/2, and show the recurrence F' = F + n
theorem main_trans (n F : ℕ) : ⟨n+1, 0, 0, 0, n, F⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, n+1, F+n⟩ := by
  -- Phase 1: R3 x (n+1): (n+1, 0, 0, 0, n, F) →* (0, 0, n+1, 0, n, F+n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, 0, n, F+n+1⟩)
  · have h := @a_to_cf 0 (n+1) 0 n F
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  -- Phase 2: R4 x n: (0, 0, n+1, 0, n, F+n+1) →* (0, 0, n+1, n, 0, F+n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, n, 0, F+n+1⟩)
  · have h := @e_to_d (n+1) 0 0 n (F+n+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 step: (0, 0, n+1, n, 0, F+n+1) → (1, 0, n+1, n+1, 0, F+n)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, n+1, n+1, 0, F+n⟩)
  · show fm ⟨0, 0, n+1, n, 0, (F+n)+1⟩ = some ⟨0+1, 0, n+1, n+1, 0, F+n⟩
    simp [fm]
  -- Phase 4: R2,R1 chain x (n+1): (1, 0, n+1, n+1, 0, F+n) →* (n+2, 0, 0, 0, n+1, F+n)
  have h := @r2r1_chain (F+n) (n+1) 0 0
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, F⟩ ↦ ⟨n+1, 0, 0, 0, n, F⟩) ⟨0, 0⟩
  intro ⟨n, F⟩; exact ⟨⟨n+1, F+n⟩, main_trans n F⟩
