import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1203: [5/6, 539/2, 4/35, 3/11, 5/7, 1/5]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  0
 0  1  0  0 -1
 0  0  1 -1  0
 0  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1203

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- R4 chain: move e to b when a=0, c=0.
-- (0, b, 0, d, e+k) →* (0, b+k, 0, d, e)
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R3/R1/R1 chain: spiral phase.
-- (0, 2k+1, c+1, d+k, 0) →* (0, 1, c+k+1, d, 0)
theorem r3r1r1_chain : ∀ k, ⟨0, 2 * k + 1, c + 1, d + k, 0⟩ [fm]⊢* ⟨0, 1, c + k + 1, d, 0⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring,
        show c + 1 = (c + 1) from rfl,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm  -- R3: (2, 2k+3, c, d+k, 0)
    step fm  -- R1: (1, 2k+2, c+1, d+k, 0)
    step fm  -- R1: (0, 2k+1, c+2, d+k, 0)
    apply stepStar_trans (ih (c := c + 1) (d := d))
    ring_nf; finish

-- R3/R2/R2 chain: drain phase.
-- (0, 0, k, d+k, e) →* (0, 0, 0, d+4*k, e+2*k)
theorem r3r2r2_chain : ∀ k, ⟨0, 0, k, d + k, e⟩ [fm]⊢* ⟨0, 0, 0, d + 4 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show d + (k + 1) = (d + k + 1) from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm  -- R3: (2, 0, k, d+k, e)
    step fm  -- R2: (1, 0, k, d+k+2, e+1)
    step fm  -- R2: (0, 0, k, d+k+4, e+2)
    rw [show d + k + 4 = (d + 4) + k from by ring]
    apply stepStar_trans (ih (d := d + 4) (e := e + 2))
    ring_nf; finish

-- Tail step: R3 + R1 + R2 from (0, 1, c+1, d+1, 0) → (0, 0, c+1, d+2, 1)
theorem tail_step : ⟨0, 1, c + 1, d + 1, 0⟩ [fm]⊢* ⟨0, 0, c + 1, d + 2, 1⟩ := by
  step fm  -- R3: (2, 1, c, d, 0)
  step fm  -- R1: (1, 0, c+1, d, 0)
  step fm  -- R2: (0, 0, c+1, d+2, 1)
  finish

-- Main transition: (0, 0, 0, n²+2n+2, 2n+1) ⊢⁺ (0, 0, 0, n²+4n+5, 2n+3)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n * n + 2 * n + 2, 2 * n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, n * n + 4 * n + 5, 2 * n + 3⟩ := by
  -- Phase 1: R4 chain: (0,0,0,n²+2n+2,2n+1) →* (0,2n+1,0,n²+2n+2,0)
  have phase1 : ⟨0, 0, 0, n * n + 2 * n + 2, 2 * n + 1⟩ [fm]⊢*
      ⟨0, 2 * n + 1, 0, n * n + 2 * n + 2, 0⟩ := by
    rw [show 2 * n + 1 = 0 + (2 * n + 1) from by ring]
    apply stepStar_trans (e_to_b (2 * n + 1) (b := 0) (d := n * n + 2 * n + 2) (e := 0))
    ring_nf; finish
  -- Phase 2: R5 step: (0, 2n+1, 0, n²+2n+2, 0) ⊢ (0, 2n+1, 1, n²+2n+1, 0)
  have phase2 : ⟨0, 2 * n + 1, 0, n * n + 2 * n + 2, 0⟩ [fm]⊢
      ⟨0, 2 * n + 1, 1, n * n + 2 * n + 1, 0⟩ := by
    rw [show n * n + 2 * n + 2 = (n * n + 2 * n + 1) + 1 from by ring]
    simp [fm]
  -- Phase 3: R3/R1/R1 chain: (0, 2n+1, 1, n²+2n+1, 0) →* (0, 1, n+1, n²+n+1, 0)
  have phase3 : ⟨0, 2 * n + 1, 1, n * n + 2 * n + 1, 0⟩ [fm]⊢*
      ⟨0, 1, n + 1, n * n + n + 1, 0⟩ := by
    rw [show n * n + 2 * n + 1 = (n * n + n + 1) + n from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (r3r1r1_chain n (c := 0) (d := n * n + n + 1))
    ring_nf; finish
  -- Phase 4: tail step: (0, 1, n+1, n²+n+1, 0) →* (0, 0, n+1, n²+n+2, 1)
  have phase4 : ⟨0, 1, n + 1, n * n + n + 1, 0⟩ [fm]⊢*
      ⟨0, 0, n + 1, n * n + n + 2, 1⟩ := by
    rw [show n + 1 = n + 1 from rfl,
        show n * n + n + 1 = (n * n + n) + 1 from by ring]
    apply stepStar_trans (tail_step (c := n) (d := n * n + n))
    ring_nf; finish
  -- Phase 5: R3/R2/R2 chain: (0, 0, n+1, n²+n+2, 1) →* (0, 0, 0, n²+4n+5, 2n+3)
  have phase5 : ⟨0, 0, n + 1, n * n + n + 2, 1⟩ [fm]⊢*
      ⟨0, 0, 0, n * n + 4 * n + 5, 2 * n + 3⟩ := by
    rw [show n * n + n + 2 = (n * n + 1) + (n + 1) from by ring]
    apply stepStar_trans (r3r2r2_chain (n + 1) (d := n * n + 1) (e := 1))
    ring_nf; finish
  -- Combine: phase1 (⊢*) + phase2 (⊢) = ⊢⁺, then chain with ⊢*
  exact stepPlus_stepStar_stepPlus
    (stepPlus_stepStar_stepPlus
      (stepPlus_stepStar_stepPlus
        (stepStar_step_stepPlus phase1 phase2)
        phase3)
      phase4)
    phase5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n * n + 2 * n + 2, 2 * n + 1⟩) 0
  intro n; exists n + 1
  show ⟨0, 0, 0, n * n + 2 * n + 2, 2 * n + 1⟩ [fm]⊢⁺
       ⟨0, 0, 0, (n + 1) * (n + 1) + 2 * (n + 1) + 2, 2 * (n + 1) + 1⟩
  rw [show (n + 1) * (n + 1) + 2 * (n + 1) + 2 = n * n + 4 * n + 5 from by ring,
      show 2 * (n + 1) + 1 = 2 * n + 3 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1203
