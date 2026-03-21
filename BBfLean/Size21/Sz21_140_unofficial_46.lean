import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #46: [35/6, 4/55, 143/2, 3/7, 14/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_46

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

-- Phase 1: R4 repeated: d → b (when a=0, c=0)
theorem d_to_b : ∀ k, ∀ b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k h <;> intro b e f
  · exists 0
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2 chain: clears c when b=0
-- (A+1, 0, C, D, C+1, F) →* (A+2*C+1, 0, 0, D, 1, F)
theorem chain_r2 : ∀ C, ∀ A D F, ⟨A+1, 0, C, D, C+1, F⟩ [fm]⊢* ⟨A+2*C+1, 0, 0, D, 1, F⟩ := by
  intro C; induction' C with C ih <;> intro A D F
  · exists 0
  -- State: (A+1, 0, C+1, D, C+2, F)
  -- R2 fires (c+1=C+1+1, e+1=C+2, R1 doesn't match since b=0)
  rw [show C + 1 + 1 = (C + 1) + 1 from rfl]
  step fm
  -- After R2: (A+3, 0, C, D, C+1, F)
  apply stepStar_trans (ih (A + 2) D F)
  ring_nf; finish

-- General chain: (A+1, B, C, D, B+C+1, F) →* (A+B+2*C+1, 0, 0, D+B, 1, F)
-- Induction on B, case split on A in inductive step
theorem chain_gen : ∀ B, ∀ A C D F, ⟨A+1, B, C, D, B+C+1, F⟩ [fm]⊢* ⟨A+B+2*C+1, 0, 0, D+B, 1, F⟩ := by
  intro B; induction' B with B ih <;> intro A C D F
  · -- Base: B=0, use chain_r2
    have h := chain_r2 C A D F
    simp only [Nat.zero_add, Nat.add_zero] at h ⊢; exact h
  -- Inductive step: B+1
  -- State: (A+1, B+1, C, D, B+C+2, F)
  -- R1 fires (a+1=A+1 ≥ 1, b+1=B+1 ≥ 1)
  rw [show B + 1 + C + 1 = B + (C + 1) + 1 from by ring]
  step fm
  -- After R1: (A, B, C+1, D+1, B+(C+1)+1, F)
  -- Case split on A
  rcases A with _ | A'
  · -- A = 0: state is (0, B, C+1, D+1, B+C+2, F)
    -- R2 fires (c+1 ≥ 1, e+1 ≥ 1, R1 doesn't match since a=0)
    rw [show B + (C + 1) + 1 = (B + C + 1) + 1 from by ring]
    step fm
    -- After R2: (2, B, C, D+1, B+C+1, F) = (1+1, B, C, D+1, B+C+1, F)
    apply stepStar_trans (ih 1 C (D + 1) F)
    ring_nf; finish
  · -- A = A'+1: state is (A'+1, B, C+1, D+1, B+(C+1)+1, F)
    apply stepStar_trans (ih A' (C + 1) (D + 1) F)
    ring_nf; finish

-- Phase 3: R3 repeated: a → e,f (when b=0, c=0)
theorem a_to_ef : ∀ k, ∀ d e f, ⟨k, 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k h <;> intro d e f
  · exists 0
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: (0, 0, 0, n, n+1, T+1) →⁺ (0, 0, 0, n+1, n+2, T+n+1)
theorem main_trans : ∀ n T, ⟨0, 0, 0, n, n + 1, T + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 1, n + 2, T + n + 1⟩ := by
  intro n T
  -- Phase 1: R4 × n: (0, 0, 0, n, n+1, T+1) →* (0, n, 0, 0, n+1, T+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, n, 0, 0, n + 1, T + 1⟩)
  · have h := d_to_b n 0 (n + 1) (T + 1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2a: R5 × 1: (0, n, 0, 0, n+1, T+1) → (1, n, 0, 1, n+1, T)
  apply step_stepStar_stepPlus (c₂ := ⟨1, n, 0, 1, n + 1, T⟩)
  · show fm ⟨0, n, 0, 0, n + 1, T + 1⟩ = some ⟨1, n, 0, 1, n + 1, T⟩; simp [fm]
  -- Phase 2b: chain: (1, n, 0, 1, n+1, T) →* (n+1, 0, 0, n+1, 1, T)
  -- Use chain_gen with A=0, B=n, C=0, D=1, F=T
  apply stepStar_trans (c₂ := ⟨n + 1, 0, 0, n + 1, 1, T⟩)
  · have h := chain_gen n 0 0 1 T
    simp only [Nat.zero_add, Nat.add_zero, Nat.mul_zero] at h
    rw [show (1 : ℕ) + n = n + 1 from by ring] at h; exact h
  -- Phase 3: R3 × (n+1): (n+1, 0, 0, n+1, 1, T) →* (0, 0, 0, n+1, n+2, T+n+1)
  have h := a_to_ef (n + 1) (n + 1) 1 T
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, T⟩ ↦ ⟨0, 0, 0, n, n + 1, T + 1⟩) ⟨0, 0⟩
  intro ⟨n, T⟩; exact ⟨⟨n + 1, T + n⟩, by
    show ⟨0, 0, 0, n, n + 1, T + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 1, n + 1 + 1, T + n + 1⟩
    exact main_trans n T⟩
