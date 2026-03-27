import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #272: [14/15, 18/7, 1/6, 625/2, 7/5]

Vector representation:
```
 1 -1 -1  1
 1  2  0 -1
-1 -1  0  0
-1  0  4  0
 0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_272

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+4, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

-- R4 chain: (A+k, 0, C, 0) →* (A, 0, C+4*k, 0)
theorem r4_chain : ∀ k A C, ⟨A+k, 0, C, 0⟩ [fm]⊢* ⟨A, (0 : ℕ), C+4*k, 0⟩ := by
  intro k; induction k with
  | zero => intro A C; exists 0
  | succ k ih =>
    intro A C
    rw [show A + (k + 1) = (A + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R2 chain: (A, B, 0, D+k) →* (A+k, B+2*k, 0, D)
theorem r2_chain : ∀ k A B D, ⟨A, B, 0, D+k⟩ [fm]⊢* ⟨A+k, B+2*k, (0 : ℕ), D⟩ := by
  intro k; induction k with
  | zero => intro A B D; exists 0
  | succ k ih =>
    intro A B D
    rw [show D + (k + 1) = (D + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R3 chain: (A+k, B+k, 0, 0) →* (A, B, 0, 0)
theorem r3_chain : ∀ k A B, ⟨A+k, B+k, 0, 0⟩ [fm]⊢* ⟨A, B, (0 : ℕ), 0⟩ := by
  intro k; induction k with
  | zero => intro A B; exists 0
  | succ k ih =>
    intro A B
    rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show B + (k + 1) = (B + k) + 1 from by ring]
    step fm
    exact ih _ _

-- mixing_loop: (A, 2, 2*j+1, k) →* (A+3*j, 2, 1, k+j)
-- Each iteration does R1,R1,R2 consuming 2 from c and adding 3 to a, 1 to d
theorem mixing_loop : ∀ j A k, ⟨A, 2, 2*j+1, k⟩ [fm]⊢* ⟨A+3*j, (2 : ℕ), 1, k+j⟩ := by
  intro j; induction j with
  | zero => intro A k; simp; exists 0
  | succ j ih =>
    intro A k
    -- State: (A, 2, 2*(j+1)+1, k) = (A, 2, 2*j+3, k)
    -- Need to expose as (A, b+1, c+1, k) for R1
    rw [show 2 * (j + 1) + 1 = (2 * j + 2) + 1 from by ring,
        show (2 : ℕ) = 0 + 1 + 1 from by ring]
    -- R1: (A, 0+1+1, (2*j+2)+1, k) → (A+1, 0+1, 2*j+2, k+1)
    step fm
    -- After step fm + simp: (A + 1, 1, 2 * j + 2, k + 1)
    -- Need to expose for R1 again
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2 * j + 2 = (2 * j + 1) + 1 from by ring]
    -- R1: (A+1, 0+1, (2*j+1)+1, k+1) → (A+2, 0, 2*j+1, k+2)
    step fm
    -- After step fm + simp: (A + 2, 0, 2 * j + 1, k + 2)
    -- Now d = k+2 ≥ 1, c might or might not be 0. But 2*j+1 ≥ 1.
    -- R5 needs a=0,b=0. R2 needs d+1. But match order: R1 first (b+1,c+1), then R2 (d+1).
    -- b=0, so R1 doesn't match. d = k+2 ≥ 1, so R2 fires.
    rw [show k + 2 = (k + 1) + 1 from by ring]
    -- R2: (A+2, 0, 2*j+1, (k+1)+1) → (A+3, 2, 2*j+1, k+1)
    step fm
    -- After step fm + simp: (A + 3, 2, 2 * j + 1, k + 1)
    apply stepStar_trans (ih (A+3) (k+1))
    ring_nf; finish

-- Full mixing phase: (1, 2, 2*K+1, 0) →* (4*K+3, 2*K+3, 0, 0)
theorem mixing (K : ℕ) : ⟨1, 2, 2*K+1, 0⟩ [fm]⊢* ⟨4*K+3, 2*K+3, (0 : ℕ), 0⟩ := by
  -- Phase 1: triple loop
  apply stepStar_trans (mixing_loop K 1 0)
  -- State: (1+3*K, 2, 1, K) = (3*K+1, 2, 1, K)
  -- R1: need b+1, c+1 pattern
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring,
      show 1 + 3 * K = 3 * K + 1 from by ring,
      show 0 + K = K from by ring]
  -- R1: (3*K+1, 0+1+1, 0+1, K) → (3*K+2, 0+1, 0, K+1)
  step fm
  -- After step fm: (3 * K + 2, 1, 0, K + 1)
  -- R2 chain: (3*K+2, 1, 0, 0+(K+1)) →* (3*K+2+(K+1), 1+2*(K+1), 0, 0)
  rw [show (1 : ℕ) = 1 from rfl]
  have h := r2_chain (K+1) (3*K+2) 1 0
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

-- Two initial steps: (0, 0, C+1, 0) →* (1, 2, C, 0) via R5 then R2
theorem init_steps (C : ℕ) : ⟨0, 0, C+1, 0⟩ [fm]⊢* ⟨1, (2 : ℕ), C, 0⟩ := by
  rw [show C + 1 = C + 1 from rfl,
      show (0 : ℕ) = 0 from rfl]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  finish

-- Full transition: (A+1, 0, 0, 0) ⊢⁺ (4*A+2, 0, 0, 0)
theorem main_trans (A : ℕ) : ⟨A+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨4*A+2, (0 : ℕ), 0, 0⟩ := by
  -- R4 chain: (A+1, 0, 0, 0) →* (0, 0, 4A+4, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 4*A+4, 0⟩)
  · have h := r4_chain (A+1) 0 0
    simp only [Nat.zero_add] at h
    rw [show 4 * (A + 1) = 4 * A + 4 from by ring] at h
    exact h
  -- Two init steps: (0, 0, 4A+4, 0) →* (1, 2, 4A+3, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 2, 4*A+3, 0⟩)
  · rw [show 4 * A + 4 = (4 * A + 3) + 1 from by ring]
    exact init_steps (4*A+3)
  -- Mixing: (1, 2, 2*(2A+1)+1, 0) →* (4*(2A+1)+3, 2*(2A+1)+3, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨4*(2*A+1)+3, 2*(2*A+1)+3, 0, 0⟩)
  · rw [show 4 * A + 3 = 2 * (2 * A + 1) + 1 from by ring]
    exact mixing (2*A+1)
  -- R3 chain: (8A+7, 4A+5, 0, 0) ⊢⁺ (4A+2, 0, 0, 0)
  -- One R3 step to get stepPlus, then r3_chain for the rest
  rw [show 4 * (2 * A + 1) + 3 = (4 * (2 * A + 1) + 2) + 1 from by ring,
      show 2 * (2 * A + 1) + 3 = (2 * (2 * A + 1) + 2) + 1 from by ring]
  step fm
  have h := r3_chain (2*(2*A+1)+2) (4*A+2) 0
  rw [show (0 : ℕ) + (2 * (2 * A + 1) + 2) = 2 * (2 * A + 1) + 2 from by ring,
      show 4 * A + 2 + (2 * (2 * A + 1) + 2) = 4 * (2 * A + 1) + 2 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0⟩) (by execute fm 14)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 0⟩) 0
  intro n
  refine ⟨4*n+4, ?_⟩
  show ⟨n+2, 0, 0, 0⟩ [fm]⊢⁺ ⟨4*n+4+2, 0, 0, 0⟩
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show 4 * n + 4 + 2 = 4 * (n + 1) + 2 from by ring]
  exact main_trans (n+1)

end Sz22_2003_unofficial_272
