import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #643: [35/6, 143/2, 4/55, 3/7, 98/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  0  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_643

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+2, e, f⟩
  | _ => none

-- R4 repeated: transfer d to b
theorem d_to_b : ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by omega]
    step fm
    apply stepStar_trans (h _)
    rw [show b + 1 + k = b + (k + 1) from by omega]; finish
  exact many_step k b

-- Interleaved round: R1, R3, R1
theorem interleaved_round : ⟨1, b+2, c, d, e+1, f⟩ [fm]⊢* ⟨1, b, c+1, d+2, e, f⟩ := by
  step fm; step fm; step fm; finish

-- Interleaved chain: k rounds
theorem interleaved_chain : ⟨1, 2*k, c, d, e+k, f⟩ [fm]⊢* ⟨1, 0, c+k, d+2*k, e, f⟩ := by
  have many_step : ∀ k c d e, ⟨1, 2*k, c, d, e+k, f⟩ [fm]⊢* ⟨1, 0, c+k, d+2*k, e, f⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [show 2 * (k + 1) = (2 * k) + 2 from by omega,
        show e + (k + 1) = (e + k) + 1 from by omega]
    apply stepStar_trans interleaved_round
    apply stepStar_trans (h _ _ _)
    rw [show c + 1 + k = c + (k + 1) from by omega,
        show d + 2 + 2 * k = d + 2 * (k + 1) from by omega]; finish
  exact many_step k c d e

-- Drain round: R3, R2, R2
theorem drain_round : ⟨0, 0, c+1, d, e+1, f⟩ [fm]⊢* ⟨0, 0, c, d, e+2, f+2⟩ := by
  step fm; step fm; step fm; finish

-- Drain chain: k rounds
theorem drain_chain : ⟨0, 0, c+k, d, e+1, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1, f+2*k⟩ := by
  have many_step : ∀ k c e f, ⟨0, 0, c+k, d, e+1, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1, f+2*k⟩ := by
    intro k; induction' k with k h <;> intro c e f
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by omega]
    apply stepStar_trans drain_round
    apply stepStar_trans (h _ _ _)
    rw [show e + 1 + k + 1 = e + (k + 1) + 1 from by omega,
        show f + 2 + 2 * k = f + 2 * (k + 1) from by omega]; finish
  exact many_step k c e f

-- Main transition
theorem main_trans (n g : ℕ) :
    (⟨0, 0, 0, 2*(n+1), (n+1)+1, g+1⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, 2*(n+2), (n+2)+1, g+2*(n+1)+1⟩ := by
  -- Phase 1: d_to_b: (0,0,0,2*(n+1),n+2,g+1) →* (0,2*(n+1),0,0,n+2,g+1)
  rw [show (2*(n+1) : ℕ) = 0 + 2*(n+1) from by omega]
  apply stepStar_stepPlus_stepPlus (@d_to_b 0 0 (2*(n+1)) (n+1+1) (g+1))
  rw [show (0 : ℕ) + 2*(n+1) = 2*(n+1) from by omega]
  -- Phase 2: R5 step: (0,2*(n+1),0,0,n+2,g+1) → (1,2*(n+1),0,2,n+2,g)
  step fm
  -- Phase 3: interleaved chain: (1,2*(n+1),0,2,1+(n+1),g) →* (1,0,n+1,2+2*(n+1),1,g)
  rw [show (n+1+1 : ℕ) = 1 + (n+1) from by omega]
  apply stepStar_trans (@interleaved_chain (n+1) 0 2 1 g)
  -- Now at (1, 0, 0+(n+1), 2+2*(n+1), 1, g) = (1, 0, n+1, 2*n+4, 1, g)
  rw [show (0 : ℕ) + (n+1) = n+1 from by omega,
      show (2 : ℕ) + 2*(n+1) = 2*n+4 from by omega]
  -- Phase 4: R2 step: (1,0,n+1,2*n+4,1,g) → (0,0,n+1,2*n+4,2,g+1)
  step fm
  -- Phase 5: drain chain
  rw [show (n+1 : ℕ) = 0 + (n+1) from by omega,
      show (2 : ℕ) = 1 + 1 from by omega]
  apply stepStar_trans drain_chain
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, g⟩ ↦ ⟨0, 0, 0, 2*(n+1), (n+1)+1, g+1⟩) ⟨0, 0⟩
  intro ⟨n, g⟩; exact ⟨⟨n+1, g+2*(n+1)⟩, main_trans n g⟩
