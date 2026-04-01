import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1394: [63/10, 9317/2, 2/33, 5/7, 3/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  1  3
 1 -1  0  0 -1
 0  0  1 -1  0
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1394

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+3⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: transfer d to c
theorem d_to_c : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e); ring_nf; finish

-- R1+R3 interleaved chain: each round does R1 then R3
-- (1, b, c+k, d, e+k) →* (1, b+k, c, d+k, e)
theorem r1r3_chain : ∀ k b c d e, ⟨1, b, c + k, d, e + k⟩ [fm]⊢* ⟨1, b + k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) c (d + 1) e); ring_nf; finish

-- R3+R2 interleaved chain: each round does R3 then R2
-- (0, b+k, 0, d, e+1) →* (0, b, 0, d+k, e+2*k+1)
theorem r3r2_chain : ∀ k b d e, ⟨0, b + k, 0, d, e + 1⟩ [fm]⊢* ⟨0, b, 0, d + k, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b (d + 1) (e + 2)); ring_nf; finish

-- Main transition: (0, 0, 0, 2n+1, 2n+3) ⊢⁺ (0, 0, 0, 4n+3, 4n+5)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 2 * n + 1, 2 * n + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * n + 3, 4 * n + 5⟩ := by
  -- Phase 1: R4 chain, transfer d to c
  -- (0, 0, 0, 2n+1, 2n+3) →* (0, 0, 2n+1, 0, 2n+3)
  have phase1 : ⟨0, 0, 0, 2 * n + 1, 2 * n + 3⟩ [fm]⊢*
      ⟨0, 0, 2 * n + 1, 0, 2 * n + 3⟩ := by
    rw [show 2 * n + 1 = 0 + (2 * n + 1) from by ring]
    exact d_to_c (2 * n + 1) 0 0 (2 * n + 3)
  -- Phase 2: R5 + R3 (two steps)
  -- (0, 0, 2n+1, 0, 2n+3) → (0, 1, 2n+1, 0, 2n+2) → (1, 0, 2n+1, 0, 2n+1)
  have phase2 : ⟨0, 0, 2 * n + 1, 0, 2 * n + 3⟩ [fm]⊢⁺
      ⟨1, 0, 2 * n + 1, 0, 2 * n + 1⟩ := by
    rw [show 2 * n + 3 = (2 * n + 1) + 1 + 1 from by ring]
    step fm; step fm; finish
  -- Phase 3: R1+R3 chain (2n+1 rounds)
  -- (1, 0, 2n+1, 0, 2n+1) →* (1, 2n+1, 0, 2n+1, 0)
  have phase3 : ⟨1, 0, 2 * n + 1, 0, 2 * n + 1⟩ [fm]⊢*
      ⟨1, 2 * n + 1, 0, 2 * n + 1, 0⟩ := by
    rw [show 2 * n + 1 = 0 + (2 * n + 1) from by ring] at *
    exact r1r3_chain (2 * n + 1) 0 0 0 0
  -- Phase 4: R2 (one step)
  -- (1, 2n+1, 0, 2n+1, 0) → (0, 2n+1, 0, 2n+2, 3)
  have phase4 : ⟨1, 2 * n + 1, 0, 2 * n + 1, 0⟩ [fm]⊢⁺
      ⟨0, 2 * n + 1, 0, 2 * n + 2, 3⟩ := by
    step fm; finish
  -- Phase 5: R3+R2 chain (2n+1 rounds)
  -- (0, 2n+1, 0, 2n+2, 3) →* (0, 0, 0, 4n+3, 4n+5)
  have phase5 : ⟨0, 2 * n + 1, 0, 2 * n + 2, 3⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * n + 3, 4 * n + 5⟩ := by
    rw [show 2 * n + 1 = 0 + (2 * n + 1) from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    apply stepStar_trans (r3r2_chain (2 * n + 1) 0 (2 * n + 2) 2)
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus phase1
    (stepPlus_trans phase2
      (stepStar_stepPlus_stepPlus phase3
        (stepPlus_stepStar_stepPlus phase4 phase5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n + 1, 2 * n + 3⟩) 0
  intro n; refine ⟨2 * n + 1, ?_⟩
  rw [show 2 * (2 * n + 1) + 1 = 4 * n + 3 from by ring,
      show 2 * (2 * n + 1) + 3 = 4 * n + 5 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1394
