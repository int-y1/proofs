import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1940: [9/70, 4/15, 77/2, 5/11, 15/7]

Vector representation:
```
-1  2 -1 -1  0
 2 -1 -1  0  0
-1  0  0  1  1
 0  0  1  0 -1
 0  1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1940

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: move e to c
theorem e_to_c : ∀ k c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- R5,R2: (0, 0, c+1, d+1, 0) ->* (2, 0, c+1, d, 0)
theorem r5r2 (c d : ℕ) : ⟨0, 0, c + 1, d + 1, 0⟩ [fm]⊢* ⟨2, 0, c + 1, d, 0⟩ := by
  step fm; step fm; finish

-- R1,R1,R2 chain
theorem r1r1r2_chain : ∀ k b c d, ⟨2, b, c + 3 * k, d + 2 * k, 0⟩ [fm]⊢*
    ⟨2, b + 3 * k, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    apply stepStar_trans (ih b (c + 3) (d + 2))
    step fm; step fm; step fm
    ring_nf; finish

-- b-drain: R4,R2,R3,R3 cycle
theorem b_drain : ∀ k d e, ⟨0, k, 0, d, e + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

-- e_to_c_r5r2: (0,0,0,d+1,e+1) ⊢⁺ (2,0,e+1,d,0)
theorem e_to_c_r5r2 (d e : ℕ) : ⟨0, 0, 0, d + 1, e + 1⟩ [fm]⊢⁺ ⟨2, 0, e + 1, d, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, d + 1, e + 1⟩ = some ⟨0, 0, 1, d + 1, e⟩
    simp [fm]
  apply stepStar_trans (e_to_c e 1 (d + 1))
  rw [show 1 + e = e + 1 from by ring]
  exact r5r2 e d

-- Step 1: (0,0,0, D+6m+3, 6m+3) ⊢⁺ (0,0,0, D+14m+8, 6m+5)
theorem step1_trans : ⟨0, 0, 0, D + 6 * m + 3, 6 * m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, D + 14 * m + 8, 6 * m + 5⟩ := by
  rw [show D + 6 * m + 3 = (D + 6 * m + 2) + 1 from by ring,
      show (6 * m + 3 : ℕ) = (6 * m + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (e_to_c_r5r2 (D + 6 * m + 2) (6 * m + 2))
  -- State: (2, 0, 6m+3, D+6m+2, 0).
  rw [show (6 * m + 2 + 1 : ℕ) = 0 + 3 * (2 * m + 1) from by ring,
      show D + 6 * m + 2 = D + 2 * m + 2 * (2 * m + 1) from by ring]
  apply stepStar_trans (r1r1r2_chain (2 * m + 1) 0 0 (D + 2 * m))
  -- State: (2, 6m+3, 0, D+2m, 0). R3, R3.
  rw [show (0 : ℕ) + 3 * (2 * m + 1) = 6 * m + 3 from by ring]
  step fm; step fm
  rw [show D + 2 * m + 1 + 1 = D + 2 * m + 2 from by ring]
  -- State: (0, 6m+3, 0, D+2m+2, 2). b_drain.
  apply stepStar_trans (b_drain (6 * m + 3) (D + 2 * m + 2) 1)
  ring_nf; finish

-- Step 2: (0,0,0, D+14m+8, 6m+5) ⊢⁺ (0,0,0, D+22m+18, 6m+9)
theorem step2_trans : ⟨0, 0, 0, D + 14 * m + 8, 6 * m + 5⟩ [fm]⊢⁺
    ⟨0, 0, 0, D + 22 * m + 18, 6 * m + 9⟩ := by
  rw [show D + 14 * m + 8 = (D + 14 * m + 7) + 1 from by ring,
      show (6 * m + 5 : ℕ) = (6 * m + 4) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (e_to_c_r5r2 (D + 14 * m + 7) (6 * m + 4))
  -- State: (2, 0, 6m+5, D+14m+7, 0). Chain (2m+1).
  rw [show (6 * m + 4 + 1 : ℕ) = 2 + 3 * (2 * m + 1) from by ring,
      show D + 14 * m + 7 = D + 10 * m + 5 + 2 * (2 * m + 1) from by ring]
  apply stepStar_trans (r1r1r2_chain (2 * m + 1) 0 2 (D + 10 * m + 5))
  -- State: (2, 6m+3, 2, D+10m+5, 0). R1, R1.
  rw [show (0 : ℕ) + 3 * (2 * m + 1) = 6 * m + 3 from by ring]
  step fm; step fm
  -- State: (0, 6m+7, 0, D+10m+3, 0).
  -- Use step_stepStar to prove R5,R2 via r5r2 on the first two components.
  -- Actually (0, 6m+7, 0, D+10m+3, 0) doesn't match r5r2 directly.
  -- r5r2 needs (0, 0, c+1, d+1, 0). Here b = 6m+7 != 0.
  -- We need R5: (0, 6m+7, 0, (D+10m+2)+1, 0) -> (0, 6m+8, 1, D+10m+2, 0)
  -- Then R2: (0, 6m+8, 1, D+10m+2, 0) -> (2, 6m+7, 0, D+10m+2, 0)
  rw [show 6 * m + 3 + 2 + 2 = 6 * m + 7 from by ring,
      show D + 10 * m + 3 = (D + 10 * m + 2) + 1 from by ring]
  step fm; step fm
  -- State: (2, 6m+7, 0, D+10m+2, 0). R3, R3.
  step fm; step fm
  rw [show D + 10 * m + 2 + 1 + 1 = D + 10 * m + 4 from by ring]
  -- State: (0, 6m+7, 0, D+10m+4, 2). b_drain.
  apply stepStar_trans (b_drain (6 * m + 7) (D + 10 * m + 4) 1)
  ring_nf; finish

-- Two-step macro
theorem macro_trans : ⟨0, 0, 0, D + 6 * m + 3, 6 * m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, D + 22 * m + 18, 6 * m + 9⟩ :=
  stepPlus_trans step1_trans step2_trans

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 3⟩) (by execute fm 14)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨D, m⟩ ↦ ⟨0, 0, 0, D + 6 * m + 3, 6 * m + 3⟩) ⟨1, 0⟩
  intro ⟨D, m⟩
  refine ⟨⟨D + 16 * m + 9, m + 1⟩, ?_⟩
  show ⟨0, 0, 0, D + 6 * m + 3, 6 * m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, D + 16 * m + 9 + 6 * (m + 1) + 3, 6 * (m + 1) + 3⟩
  rw [show D + 16 * m + 9 + 6 * (m + 1) + 3 = D + 22 * m + 18 from by ring,
      show 6 * (m + 1) + 3 = 6 * m + 9 from by ring]
  exact macro_trans
