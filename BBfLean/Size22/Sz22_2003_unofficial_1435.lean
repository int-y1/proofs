import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1435: [7/15, 22/3, 99/70, 5/11, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  1
-1  2 -1 -1  1
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1435

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: move e to c
theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- Crunch: (k+1, 0, 3k+2, d+1, e) ->* (0, 1, 0, d+k+1, e+k+1)
theorem crunch : ∀ k, ∀ d e, ⟨k + 1, 0, 3 * k + 2, d + 1, e⟩ [fm]⊢* ⟨0, 1, 0, d + k + 1, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · -- base: (1, 0, 2, d+1, e) -> R3 -> (0, 2, 1, d, e+1) -> R1 -> (0, 1, 0, d+1, e+1)
    step fm; step fm; finish
  · -- step: (k+2, 0, 3k+5, d+1, e) -> R3,R1,R1 -> (k+1, 0, 3k+2, d+2, e+1)
    rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 3 from by ring,
        show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 1) (e := e + 1))
    ring_nf; finish

-- Drain: (k+1, 0, 0, d+1, e+1) ->* (k+d+2, 0, 0, 0, e+2*d+3)
theorem drain : ∀ d, ∀ k e, ⟨k + 1, 0, 0, d + 1, e + 1⟩ [fm]⊢* ⟨k + d + 2, 0, 0, 0, e + 2 * d + 3⟩ := by
  intro d; induction' d with d ih <;> intro k e
  · -- base: (k+1, 0, 0, 1, e+1) -> R4,R3,R2,R2 -> (k+2, 0, 0, 0, e+3)
    step fm; step fm; step fm; step fm; finish
  · -- step: (k+1, 0, 0, d+2, e+1) -> R4,R3,R2,R2 -> (k+2, 0, 0, d+1, e+3)
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show e + 1 + 1 + 1 = (e + 2) + 1 from by ring,
        show k + 1 + 1 = (k + 1) + 1 from by ring]
    apply stepStar_trans (ih (k := k + 1) (e := e + 2))
    ring_nf; finish

-- Main transition: (n+2, 0, 0, 0, 3n+3) ⊢⁺ (n+3, 0, 0, 0, 3n+6)
theorem main_trans : ⟨n + 2, 0, 0, 0, 3 * n + 3⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 3 * n + 6⟩ := by
  -- Phase 1: e_to_c
  rw [show 3 * n + 3 = 0 + (3 * n + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (3 * n + 3) (a := n + 2) (c := 0) (e := 0))
  -- Now at (n+2, 0, 3n+3, 0, 0)
  -- Phase 2: R5 + R1
  rw [show 0 + (3 * n + 3) = 3 * n + 3 from by ring]
  step fm  -- R5: (n+1, 1, 3n+3, 1, 0)
  step fm  -- R1: (n+1, 0, 3n+2, 2, 0)
  -- Phase 3: crunch
  show ⟨n + 1, 0, 3 * n + 2, 1 + 1, 0⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 3 * n + 6⟩
  apply stepStar_trans (crunch n (d := 1) (e := 0))
  -- Now at (0, 1, 0, n+2, n+1)
  -- Phase 4: R2
  rw [show 1 + n + 1 = n + 2 from by ring,
      show 0 + n + 1 = n + 1 from by ring]
  step fm  -- R2: (1, 0, 0, n+2, n+2)
  -- Phase 5: drain
  show ⟨1, 0, 0, n + 2, (n + 1) + 1⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 3 * n + 6⟩
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (drain (n + 1) (k := 0) (e := n + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩)
  · execute fm 6
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 3 * n + 3⟩) 0
  intro n; exact ⟨n + 1, main_trans⟩
