import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #560: [315/2, 1/605, 2/65, 143/3, 5/77]

Vector representation:
```
-1  2  1  1  0  0
 0  0 -1  0 -2  0
 1  0 -1  0  0 -1
 0 -1  0  0  1  1
 0  0  1 -1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_560

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+2, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+2, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- Phase 1: R4 drain b to e,f: (0, b+k, 0, d, e, f) →* (0, b, 0, d, e+k, f+k)
theorem r4_drain : ⟨0, b+k, 0, d, e, f⟩ [fm]⊢* ⟨0, b, 0, d, e+k, f+k⟩ := by
  have many_step : ∀ k e f, ⟨0, b+k, 0, d, e, f⟩ [fm]⊢* ⟨0, b, 0, d, e+k, f+k⟩ := by
    intro k; induction' k with k h <;> intro e f
    · exists 0
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k e f

-- Phase 2: R5+R2 loop: (0, 0, 0, d+k, e+3*k, f) →* (0, 0, 0, d, e, f)
theorem r5r2_loop : ⟨0, 0, 0, d+k, e+3*k, f⟩ [fm]⊢* ⟨0, 0, 0, d, e, f⟩ := by
  have many_step : ∀ k d e, ⟨0, 0, 0, d+k, e+3*k, f⟩ [fm]⊢* ⟨0, 0, 0, d, e, f⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 3 * (k + 1) = (e + 3 * k) + 2 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k d e

-- Phase 4: R3+R1 loop: (0, b, 1, d, 1, f+k) →* (0, b+2*k, 1, d+k, 1, f)
theorem r3r1_loop : ⟨0, b, 1, d, 1, f+k⟩ [fm]⊢* ⟨0, b+2*k, 1, d+k, 1, f⟩ := by
  have many_step : ∀ k b d, ⟨0, b, 1, d, 1, f+k⟩ [fm]⊢* ⟨0, b+2*k, 1, d+k, 1, f⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b d

-- Main transition: (0, 3*n+2, 0, 2*n+2, 0, 1) →⁺ (0, 6*n+5, 0, 4*n+4, 0, 1)
theorem main_trans : ⟨0, 3*n+2, 0, 2*n+2, 0, 1⟩ [fm]⊢⁺ ⟨0, 6*n+5, 0, 4*n+4, 0, 1⟩ := by
  -- Phase 1: R4 drain (3n+2 steps): → (0, 0, 0, 2n+2, 3n+2, 3n+3)
  rw [show (3*n+2 : ℕ) = 0 + (3*n+2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (k := 3*n+2) (b := 0) (d := 2*n+2) (e := 0) (f := 1))
  simp only [Nat.zero_add]
  -- Phase 2: R5+R2 loop (n rounds): → (0, 0, 0, n+2, 2, 3n+3)
  rw [show (2*n+2 : ℕ) = (n+2) + n from by ring,
      show (3*n+2 : ℕ) = 2 + 3*n from by ring]
  apply stepStar_stepPlus_stepPlus r5r2_loop
  -- Phase 3: R5+R3+R1 (3 steps): → (0, 2, 1, n+2, 1, 3n+2)
  rw [show 1 + (2 + 3 * n) = (3*n+2) + 1 from by ring]
  step fm; step fm; step fm
  -- Phase 4: R3+R1 loop (3n+2 rounds): → (0, 6n+6, 1, 4n+4, 1, 0)
  rw [show (3*n+2 : ℕ) = 0 + (3*n+2) from by ring]
  apply stepStar_trans (r3r1_loop (k := 3*n+2) (b := 2) (d := n+2) (f := 0))
  -- Phase 5: R4+R2 (2 steps): → (0, 6n+5, 0, 4n+4, 0, 1)
  rw [show 2 + 2 * (3 * n + 2) = (6 * n + 5) + 1 from by ring,
      show (n + 2 + (3 * n + 2) : ℕ) = 4*n+4 from by ring]
  step fm; step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 2, 0, 1⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 3*n+2, 0, 2*n+2, 0, 1⟩) 0
  intro n; exists 2*n+1
  rw [show 3 * (2 * n + 1) + 2 = 6*n+5 from by ring,
      show 2 * (2 * n + 1) + 2 = 4*n+4 from by ring]
  exact main_trans
