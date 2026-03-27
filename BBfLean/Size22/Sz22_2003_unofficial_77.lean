import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #77: [1/18, 385/2, 14/65, 39/7, 2/33]

Vector representation:
```
-1 -2  0  0  0  0
-1  0  1  1  1  0
 1  0 -1  1  0 -1
 0  1  0 -1  0  1
 1 -1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_77

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e+1, f⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- Phase 1: R4 chain. Transfer d to b and f.
theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- Phase 2: R5+R1 chain. Each round: b decreases by 3, e decreases by 1.
theorem r5r1_chain : ∀ k, ∀ b e f, ⟨0, b + 3 * k, 0, 0, e + k, f⟩ [fm]⊢*
    ⟨0, b, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 1 + 2 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 3: R3+R2 chain, parameterized so f = k+1 in the inductive step.
theorem r3r2_chain : ∀ k, ∀ d e, ⟨0, 1, 1, d, e, k⟩ [fm]⊢* ⟨0, 1, 1, d + 2 * k, e + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  -- State: (0, 1, 1, d, e, k+1). R3 fires: c=1>=1, f=k+1>=1.
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  -- After R3: (1, 1, 0, d+1, e, k). R2 fires: a=1>=1.
  step fm
  -- After R2: (0, 1, 1, d+2, e+1, k)
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Main transition: (0, 0, 0, 3n+2, 2n+2, 0) ⊢⁺ (0, 0, 0, 6n+5, 4n+4, 0)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 3 * n + 2, 2 * n + 2, 0⟩ [fm]⊢⁺ (⟨0, 0, 0, 6 * n + 5, 4 * n + 4, 0⟩ : Q) := by
  -- Phase 1: R4 chain (3n+2 steps)
  rw [show 3 * n + 2 = 0 + (3 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (3 * n + 2) 0 0 (2 * n + 2) 0)
  simp only [Nat.zero_add]
  -- Now at (0, 3n+2, 0, 0, 2n+2, 3n+2)
  -- Phase 2: R5+R1 chain (n rounds)
  rw [show (3 * n + 2 : ℕ) = 2 + 3 * n from by ring,
      show (2 * n + 2 : ℕ) = (n + 2) + n from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain n 2 (n + 2) (2 + 3 * n))
  -- Now at (0, 2, 0, 0, n+2, 2+3n)
  -- Phase 2b: R5
  rw [show (n + 2 : ℕ) = (n + 1) + 1 from by ring,
      show (2 : ℕ) = 0 + 1 + 1 from by ring]
  step fm
  -- Now at (1, 1, 0, 0, n+1, 2+3n). But after step, n+1 might show as n+1.
  -- Phase 2c: R2
  step fm
  -- Now at (0, 1, 1, 1, n+2, 2+3n)
  -- Phase 3: R3+R2 chain
  rw [show (2 + 3 * n : ℕ) = 3 * n + 2 from by ring,
      show (n + 1 + 1 : ℕ) = n + 2 from by ring]
  -- Phase 3: R3+R2 chain
  apply stepStar_trans (r3r2_chain (3 * n + 2) 1 (n + 2))
  rw [show 1 + 2 * (3 * n + 2) = 6 * n + 5 from by ring,
      show n + 2 + (3 * n + 2) = 4 * n + 4 from by ring]
  -- Phase 4: R4, R3, R1
  rw [show (6 * n + 5 : ℕ) = (6 * n + 4) + 1 from by ring]
  step fm
  step fm
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2, 0⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 3 * n + 2, 2 * n + 2, 0⟩) 0
  intro n
  exists n + n + 1
  rw [show 3 * (n + n + 1) + 2 = 6 * n + 5 from by ring,
      show 2 * (n + n + 1) + 2 = 4 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_77
