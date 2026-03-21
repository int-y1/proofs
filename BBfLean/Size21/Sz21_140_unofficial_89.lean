import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #89: [5/6, 7/2, 44/35, 3/11, 110/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  0
 2  0 -1 -1  1
 0  1  0  0 -1
 1  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_89

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e+1⟩
  | _ => none

-- Phase 1: R4 repeated: e → b (when a=0, c=0)
theorem e_to_b : ⟨0, b, 0, d, e+k⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b e, ⟨0, b, 0, d, e+k⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b e

-- Phase 5: R3,R2,R2 chain: (0, 0, c+k, d+1, e) →* (0, 0, c, d+1+k, e+k)
theorem r3r2r2_chain : ∀ k, ∀ c d e, ⟨0, 0, c+k, d+1, e⟩ [fm]⊢* ⟨0, 0, c, d+1+k, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h c (d + 1) (e + 1))
  ring_nf; finish

-- Phase 3b: R1,R1,R3 rounds: (2, 2k+1, K, k, K+1) →* (2, 1, K+k, 0, K+k+1)
theorem r1r1r3_rounds : ∀ k, ∀ K, ⟨2, 2*k+1, K, k, K+1⟩ [fm]⊢* ⟨2, 1, K+k, 0, K+k+1⟩ := by
  intro k; induction' k with k h <;> intro K
  · exists 0
  -- (2, 2*(k+1)+1, K, k+1, K+1) = (2, 2*k+3, K, k+1, K+1)
  -- R1: (1, 2*k+2, K+1, k+1, K+1)
  -- R1: (0, 2*k+1, K+2, k+1, K+1)
  -- R3: (2, 2*k+1, K+1, k, K+2)
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
  step fm; step fm
  rw [show K + 2 = (K + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (h (K + 1))
  ring_nf; finish

-- Main transition: C(n) = (0, 0, 0, n+2, 2*n+2) →⁺ C(n+1) = (0, 0, 0, n+3, 2*n+4)
theorem main_trans (n : ℕ) : ⟨0, 0, 0, n+2, 2*n+2⟩ [fm]⊢⁺ ⟨0, 0, 0, n+3, 2*n+4⟩ := by
  -- Phase 1: e → b: (0, 0, 0, n+2, 2*n+2) →* (0, 2*n+2, 0, n+2, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*n+2, 0, n+2, 0⟩)
  · have h := @e_to_b 0 (n+2) 0 (2*n+2)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5: (0, 2*n+2, 0, n+2, 0) → (1, 2*n+2, 1, n+1, 1)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2*n+2, 1, n+1, 1⟩)
  · show fm ⟨0, 2*n+2, 0, (n+1)+1, 0⟩ = some ⟨1, 2*n+2, 1, n+1, 1⟩
    rw [show (n+1)+1 = n+2 from by ring]; simp [fm]
  -- Phase 3a: R1,R3: (1, 2*n+2, 1, n+1, 1) → (0, 2*n+1, 2, n+1, 1) → (2, 2*n+1, 1, n, 2)
  apply stepStar_trans (c₂ := ⟨2, 2*n+1, 1, n, 2⟩)
  · rw [show 2*n+2 = (2*n+1) + 1 from by ring]
    step fm
    rw [show (n+1) = n + 1 from by ring]
    step fm
    finish
  -- Phase 3b: R1,R1,R3 rounds: (2, 2*n+1, 1, n, 2) →* (2, 1, n+1, 0, n+2)
  apply stepStar_trans (c₂ := ⟨2, 1, n+1, 0, n+2⟩)
  · have h := @r1r1r3_rounds n 1
    convert h using 2; ring_nf
  -- Phase 3c: Final R1: (2, 1, n+1, 0, n+2) → (1, 0, n+2, 0, n+2)
  apply stepStar_trans (c₂ := ⟨1, 0, n+2, 0, n+2⟩)
  · rw [show 1 = 0 + 1 from by ring, show n + 2 = (n+1) + 1 from by ring]
    step fm
    rw [show n + 1 + 1 = n + 2 from by ring]
    finish
  -- Phase 4: R2: (1, 0, n+2, 0, n+2) → (0, 0, n+2, 1, n+2)
  apply stepStar_trans (c₂ := ⟨0, 0, n+2, 1, n+2⟩)
  · step fm; finish
  -- Phase 5: R3,R2,R2 chain: (0, 0, n+2, 1, n+2) →* (0, 0, 0, n+3, 2*n+4)
  have h := @r3r2r2_chain (n+2) 0 0 (n+2)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, 0, n+2, 2*n+2⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩
