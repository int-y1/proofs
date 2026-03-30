import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #855: [36/35, 5/3, 1/10, 343/2, 6/7]

Vector representation:
```
 2  2 -1 -1
 0 -1  1  0
-1  0 -1  0
-1  0  0  3
 1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_855

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+2, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a+1, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+3⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b+1, c, d⟩
  | _ => none

-- R4 chain: (k, 0, 0, d) →* (0, 0, 0, d+3*k)
theorem r4_chain : ∀ k, ∀ d, ⟨k, 0, 0, d⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · step fm  -- R4: (k, 0, 0, d+3)
    apply stepStar_trans (ih (d + 3))
    ring_nf; finish

-- Opening: (0, 0, 0, d+3) →⁺ (3, 2, 0, d+1)
theorem opening : ⟨0, 0, 0, d + 3⟩ [fm]⊢⁺ ⟨3, 2, 0, d + 1⟩ := by
  step fm; step fm; step fm; finish

-- R2+R1 interleaved chain: (a, b+1, 0, k) →* (a+2*k, b+1+k, 0, 0)
-- Induct on k. All other vars universally quantified inside.
theorem r2r1_chain : ∀ k, ∀ a b, ⟨a, b + 1, 0, k⟩ [fm]⊢* ⟨a + 2 * k, b + 1 + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · step fm  -- R2: (a, b, 1, k+1). R1 now: c=1≥1, d=k+1≥1.
    step fm  -- R1: (a+2, b+2, 0, k)
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (b + 1))
    ring_nf; finish

-- R2 chain with accumulator: (a, k, c, 0) →* (a, 0, c+k, 0)
theorem b_to_c : ∀ k, ∀ a c, ⟨a, k, c, 0⟩ [fm]⊢* ⟨a, 0, c + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm  -- R2: (a, k, c+1, 0)
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

-- R3 chain: (a+k, 0, k, 0) →* (a, 0, 0, 0)
theorem r3_chain : ∀ k, ∀ a, ⟨a + k, 0, k, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  · -- (a+k+1, 0, k+1, 0). R1: c=k+1≥1, d=0, no. R2: b=0, no.
    -- R3: a+k+1≥1, c=k+1≥1, yes.
    step fm  -- R3: (a+k, 0, k, 0)
    exact ih a

-- Main transition: (a+1, 0, 0, 0) →⁺ (3*a+2, 0, 0, 0)
theorem main_trans : ⟨a + 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨3 * a + 2, 0, 0, 0⟩ := by
  -- Phase 1: R4 chain (a+1 times): → (0, 0, 0, 3*(a+1))
  apply stepStar_stepPlus_stepPlus (r4_chain (a + 1) 0)
  rw [show 0 + 3 * (a + 1) = 3 * a + 3 from by ring]
  -- Phase 2: opening: → (3, 2, 0, 3*a+1)
  rw [show 3 * a + 3 = 3 * a + 3 from rfl]
  apply stepPlus_stepStar_stepPlus
  · rw [show 3 * a + 3 = (3 * a) + 3 from by ring]
    exact opening
  -- Phase 3: R2+R1 chain: (3, 2, 0, 3*a+1) → (6*a+5, 3*a+3, 0, 0)
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r2r1_chain (3 * a + 1) 3 1)
  rw [show 3 + 2 * (3 * a + 1) = 6 * a + 5 from by ring,
      show 1 + 1 + (3 * a + 1) = 3 * a + 3 from by ring]
  -- Phase 4: R2 chain: (6*a+5, 3*a+3, 0, 0) → (6*a+5, 0, 3*a+3, 0)
  apply stepStar_trans (b_to_c (3 * a + 3) (6 * a + 5) 0)
  rw [show 0 + (3 * a + 3) = 3 * a + 3 from by ring,
      show 6 * a + 5 = (3 * a + 2) + (3 * a + 3) from by ring]
  -- Phase 5: R3 chain: (3*a+2 + (3*a+3), 0, 3*a+3, 0) → (3*a+2, 0, 0, 0)
  exact r3_chain (3 * a + 3) (3 * a + 2)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0⟩) 0
  intro n; exists 3 * n + 1
  rw [show 3 * n + 1 + 1 = 3 * n + 2 from by ring]
  exact main_trans
