import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #638: [35/6, 143/2, 4/55, 3/7, 42/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_638

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d+1, e, f⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, 0+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, 0, e, f⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, 0+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, 0, e, f⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [show 0 + (k + 1) = 0 + k + 1 from by ring]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R1R1R3 chain: interleaved phase consuming pairs from b
theorem r1r1r3_chain : ⟨2, b+2*k, c, d, e+k, f⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e, f⟩ := by
  have many_step : ∀ k c d e, ⟨2, b+2*k, c, d, e+k, f⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e, f⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k c d e

-- R3R2R2 chain: drain c converting to e and f (e+1 ensures R3 fires)
theorem r3r2r2_chain : ⟨0, 0, c+k, d, e+1, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1, f+2*k⟩ := by
  have many_step : ∀ k c e f, ⟨0, 0, c+k, d, e+1, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1, f+2*k⟩ := by
    intro k; induction' k with k h <;> intro c e f
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k c e f

-- Main transition: (0,0,0,2n+2,n+2,n^2+2n+2) →⁺ (0,0,0,2n+4,n+3,n^2+4n+5)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 2*n+2, n+2, n*n+2*n+2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*n+4, n+3, n*n+4*n+5⟩ := by
  -- Phase 1: R4 chain: d → b
  rw [show (2 : ℕ) * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  simp only [Nat.zero_add]
  -- Phase 2: R5, R1, R3 (3 steps)
  step fm; step fm; step fm
  -- Phase 3: R1R1R3 chain with n rounds
  rw [show (2 : ℕ) * n + 2 = 2 + 2 * n from by ring,
      show n + 1 = 1 + n from by ring]
  apply stepStar_trans r1r1r3_chain
  simp only [Nat.zero_add]
  -- Phase 4: R1, R1 (2 steps)
  step fm; step fm
  -- Phase 5: R3R2R2 chain with n+2 rounds
  rw [show (n : ℕ) + 2 = 0 + (n + 2) from by ring]
  apply stepStar_trans r3r2r2_chain
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2*n+2, n+2, n*n+2*n+2⟩) 0
  intro n; exists n + 1
  have h := main_trans n
  convert h using 2; ring_nf
