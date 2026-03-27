import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #10: [1/105, 45/22, 10/3, 7/2, 363/7]

Vector representation:
```
 0 -1 -1 -1  0
-1  2  1  0 -1
 1 -1  1  0  0
-1  0  0  1  0
 0  1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_10

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- Phase 1: Alternating R5+R1 chain, then final R5.
-- k rounds of (R5, R1) drain d from 2k+1 to 1 and c by k, then final R5.
theorem r5r1_chain : ∀ k, ∀ c e,
    ⟨0, 0, c+k, 2*k+1, e⟩ [fm]⊢* ⟨0, 1, c, 0, e+2*k+2⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · step fm; ring_nf; finish
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih c (e + 2))
  ring_nf; finish

-- Phase 2: R3+R2 interleaved chain.
-- Each pair: R3 then R2. b increases by 1, c increases by 2, e decreases by 1.
theorem r3r2_chain : ∀ k, ∀ b c,
    ⟨0, b+1, c, 0, k⟩ [fm]⊢* ⟨0, b+k+1, c+2*k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · ring_nf; finish
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (ih (b + 1) (c + 2))
  ring_nf; finish

-- Phase 3: R3 chain. b transfers to a, c increases.
theorem r3_chain : ∀ k, ∀ a c,
    ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a+k, 0, c+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih (a + 1) (c + 1))
  ring_nf; finish

-- Phase 4: R4 chain. a transfers to d.
theorem r4_chain : ∀ k, ∀ c d,
    ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih c (d + 1))
  ring_nf; finish

-- Main transition: (0, 0, c+n, 2n+1, 0) ⊢⁺ (0, 0, c+6n+7, 2n+3, 0)
theorem main_trans (c n : ℕ) :
    ⟨0, 0, c+n, 2*n+1, 0⟩ [fm]⊢⁺ ⟨0, 0, c+6*n+7, 2*n+3, 0⟩ := by
  -- Phase 1: (0, 0, c+n, 2n+1, 0) →* (0, 1, c, 0, 2n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, c, 0, 2*n+2⟩)
  · have h := r5r1_chain n c 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: (0, 1, c, 0, 2n+2) →* (0, 2n+3, c+4n+4, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*n+3, c+4*n+4, 0, 0⟩)
  · have h := r3r2_chain (2*n+2) 0 c
    simp only [Nat.zero_add] at h
    rw [show 2 * n + 2 + 1 = 2 * n + 3 from by omega,
        show c + 2 * (2 * n + 2) = c + 4 * n + 4 from by ring] at h
    exact h
  -- Phase 3: (0, 2n+3, c+4n+4, 0, 0) →* (2n+3, 0, c+6n+7, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2*n+3, 0, c+6*n+7, 0, 0⟩)
  · have h := r3_chain (2*n+3) 0 (c+4*n+4)
    simp only [Nat.zero_add] at h
    rw [show c + 4 * n + 4 + (2 * n + 3) = c + 6 * n + 7 from by ring] at h
    exact h
  -- Phase 4: (2n+3, 0, c+6n+7, 0, 0) →⁺ (0, 0, c+6n+7, 2n+3, 0)
  apply step_stepStar_stepPlus (c₂ := ⟨2*n+2, 0, c+6*n+7, 1, 0⟩)
  · show fm ⟨2*n+2+1, 0, c+6*n+7, 0, 0⟩ = some ⟨2*n+2, 0, c+6*n+7, 0+1, 0⟩
    simp [fm]
  have h := r4_chain (2*n+2) (c+6*n+7) 1
  rw [show 1 + (2 * n + 2) = 2 * n + 3 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, n⟩ ↦ ⟨0, 0, c+n, 2*n+1, 0⟩) ⟨0, 0⟩
  intro ⟨c, n⟩
  refine ⟨⟨c + 5*n + 6, n + 1⟩, ?_⟩
  show ⟨0, 0, c+n, 2*n+1, 0⟩ [fm]⊢⁺ ⟨0, 0, (c+5*n+6)+(n+1), 2*(n+1)+1, 0⟩
  rw [show (c+5*n+6)+(n+1) = c+6*n+7 from by ring,
      show 2*(n+1)+1 = 2*n+3 from by ring]
  exact main_trans c n
