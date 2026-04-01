import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1457: [7/15, 3/77, 242/3, 25/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -1
 1 -1  0  0  2
 0  0  2  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1457

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R5 fires on (a+1, 0, c, d, 0)
theorem r5_step (a c d : ℕ) : fm ⟨a + 1, 0, c, d, 0⟩ = some ⟨a, 1, c, d + 1, 0⟩ := by
  unfold fm; simp

-- Opening: (1, 0, 0, d, 0) →⁺ (1, 0, 0, d+1, 2)
theorem opening (d : ℕ) : ⟨1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, d + 1, 2⟩ := by
  apply step_stepStar_stepPlus (r5_step 0 0 d)
  step fm; finish

-- Spiral: (a, b, 0, D+1, 2) →* (a+D+1, b, 0, 0, D+3)
theorem spiral : ∀ D, ∀ a b, ⟨a, b, 0, D + 1, 2⟩ [fm]⊢* ⟨a + D + 1, b, 0, 0, D + 3⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro a b
  rcases D with _ | _ | D
  · step fm; step fm; finish
  · step fm; step fm; step fm; step fm; finish
  · step fm; step fm; step fm
    apply stepStar_trans (ih D (by omega) (a + 1) (b + 1))
    step fm; ring_nf; finish

-- R4 chain: (a, 0, c, 0, e + 2*k) →* (a, 0, c + 2*k, 0, e)
theorem r4_chain : ∀ k a c e, ⟨a, 0, c, 0, e + 2 * k⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) e)
    ring_nf; finish

-- R5/R1 chain: (a+k, 0, c+k, d, 0) →* (a, 0, c, d + 2*k, 0)
theorem r5r1_chain : ∀ k a c d, ⟨a + k, 0, c + k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm  -- R5
    step fm  -- R1
    apply stepStar_trans (ih a c (d + 2))
    ring_nf; finish

-- Drain: (n+2, 0, n+2, 0, 1) →* (n+1, 0, n, 2, 0)
theorem drain4 (n : ℕ) : ⟨n + 2, 0, n + 2, 0, 1⟩ [fm]⊢* ⟨n + 1, 0, n, 2, 0⟩ := by
  step fm  -- R5
  step fm  -- R1
  step fm  -- R2
  step fm  -- R1
  finish

-- Main transition: (1, 0, 0, 2*n, 0) →⁺ (1, 0, 0, 4*n+2, 0)
theorem main_trans (n : ℕ) : ⟨1, 0, 0, 2 * n, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 4 * n + 2, 0⟩ := by
  -- Phase 1: opening
  apply stepPlus_stepStar_stepPlus (opening (2 * n))
  -- Now at (1, 0, 0, 2*n+1, 2)
  -- Phase 2: spiral
  apply stepStar_trans (spiral (2 * n) 1 0)
  -- Now at (1 + 2*n + 1, 0, 0, 0, 2*n + 3)
  show ⟨1 + 2 * n + 1, 0, 0, 0, 2 * n + 3⟩ [fm]⊢* ⟨1, 0, 0, 4 * n + 2, 0⟩
  -- Phase 3: R4 chain
  rw [show 2 * n + 3 = 1 + 2 * (n + 1) from by ring]
  apply stepStar_trans (r4_chain (n + 1) (1 + 2 * n + 1) 0 1)
  -- Now at (2*n+2, 0, 2*(n+1), 0, 1)
  show ⟨1 + 2 * n + 1, 0, 0 + 2 * (n + 1), 0, 1⟩ [fm]⊢* ⟨1, 0, 0, 4 * n + 2, 0⟩
  -- Phase 4a: drain4
  rw [show 1 + 2 * n + 1 = 2 * n + 2 from by ring,
      show 0 + 2 * (n + 1) = 2 * n + 2 from by ring]
  apply stepStar_trans (drain4 (2 * n))
  -- Now at (2*n+1, 0, 2*n, 2, 0)
  -- Phase 4b: R5/R1 chain
  have h := r5r1_chain (2 * n) 1 0 2
  simp only [Nat.zero_add] at h
  rw [show (2 * n + 1 : ℕ) = 1 + 2 * n from by ring]
  apply stepStar_trans h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨1, 0, 0, 2 * n, 0⟩) 0
  intro n
  refine ⟨2 * n + 1, ?_⟩
  show ⟨1, 0, 0, 2 * n, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 2 * (2 * n + 1), 0⟩
  rw [show 2 * (2 * n + 1) = 4 * n + 2 from by ring]
  exact main_trans n
