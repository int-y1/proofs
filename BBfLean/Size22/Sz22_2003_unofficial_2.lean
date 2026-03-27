import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #2: [1/105, 15/22, 4/3, 35/2, 363/5]

Vector representation:
```
 0 -1 -1 -1  0
-1  1  1  0 -1
 2 -1  0  0  0
-1  0  1  1  0
 0  1 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_2

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R3 chain: a decreases, c and d increase
theorem r3_chain : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R2 chain: b decreases, a increases by 2 per step (with d=0, e=0)
theorem r2_chain : ∀ k a b c, ⟨a, b+k, c, 0, 0⟩ [fm]⊢* ⟨a+2*k, b, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4/R0 drain: alternating R4 and R0
theorem r4r0_drain : ∀ k c d e, ⟨0, 0, c+2*k, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Interleaved R1/R2 chain: (2, b, 2b+1, 0, 2k+2) →* (0, b+k+2, 2b+2k+3, 0, 0)
theorem interleaved : ∀ k b, ⟨2, b, 2*b+1, 0, 2*k+2⟩ [fm]⊢* ⟨0, b+k+2, 2*b+2*k+3, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · step fm; step fm; ring_nf; finish
  rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 from by ring]
  step fm; step fm; step fm
  rw [show 2 * b + 3 = 2 * (b + 1) + 1 from by ring]
  apply stepStar_trans (ih (b + 1))
  ring_nf; finish

-- All phases after opening: (2, 0, 1, 0, 2n+2) →* (1, 0, 0, 0, 4n+7)
theorem phases (n : ℕ) : ⟨2, 0, 1, 0, 2*n+2⟩ [fm]⊢* ⟨1, 0, 0, 0, 4*n+7⟩ := by
  -- Interleaved chain: (2, 0, 1, 0, 2n+2) →* (0, n+2, 2n+3, 0, 0)
  have h1 := interleaved n 0
  rw [show 2 * 0 + 1 = 1 from by ring,
      show 0 + n + 2 = n + 2 from by ring,
      show 2 * 0 + 2 * n + 3 = 2 * n + 3 from by ring] at h1
  apply stepStar_trans h1
  -- R2 chain: →* (2n+4, 0, 2n+3, 0, 0)
  have h2 := r2_chain (n+2) 0 0 (2*n+3)
  rw [show 0 + (n + 2) = n + 2 from by ring,
      show 0 + 2 * (n + 2) = 2 * n + 4 from by ring] at h2
  apply stepStar_trans h2
  -- R3 chain: →* (0, 0, 4n+7, 2n+4, 0)
  rw [show (2 * n + 4 : ℕ) = 0 + (2 * n + 4) from by ring]
  apply stepStar_trans (r3_chain (2*n+4) 0 (2*n+3) 0)
  rw [show 2 * n + 3 + (2 * n + 4) = 4 * n + 7 from by ring,
      show 0 + (2 * n + 4) = 2 * n + 4 from by ring]
  -- R4/R0 drain: →* (0, 0, 1, 1, 4n+6)
  have h4 := r4r0_drain (2*n+3) 1 1 0
  rw [show 1 + 2 * (2 * n + 3) = 4 * n + 7 from by ring,
      show 1 + (2 * n + 3) = 2 * n + 4 from by ring,
      show 0 + 2 * (2 * n + 3) = 4 * n + 6 from by ring] at h4
  apply stepStar_trans h4
  -- Closing: R4, R2, R1, R0 -> (1, 0, 0, 0, 4n+7)
  execute fm 4

-- Main transition: (1, 0, 0, 0, 2n+3) ⊢⁺ (1, 0, 0, 0, 4n+7)
theorem main_trans (n : ℕ) : ⟨1, 0, 0, 0, 2*n+3⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 4*n+7⟩ := by
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
  apply step_stepStar_stepPlus (by rfl : fm ⟨1, 0, 0, 0, (2 * n + 2) + 1⟩ = some ⟨0, 1, 1, 0, 2 * n + 2⟩)
  step fm
  exact phases n

-- Base case: (1, 0, 0, 0, 1) ⊢⁺ (1, 0, 0, 0, 3)
theorem base_trans : ⟨1, 0, 0, 0, 1⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 3⟩ := by
  execute fm 10

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, 0, 2*n+1⟩) 0
  intro n
  rcases n with _ | n
  · exact ⟨1, base_trans⟩
  · exact ⟨2*n+3, by
      show ⟨1, 0, 0, 0, 2*(n+1)+1⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2*(2*n+3)+1⟩
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 from by ring,
          show 2 * (2 * n + 3) + 1 = 4 * n + 7 from by ring]
      exact main_trans n⟩

end Sz22_2003_unofficial_2
