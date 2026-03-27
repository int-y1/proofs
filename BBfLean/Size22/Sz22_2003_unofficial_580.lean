import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #580: [35/6, 11/2, 4/55, 3/7, 60/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 2  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_580

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: convert d to b (a=0, c=0)
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _); ring_nf; finish
  exact many_step k b

-- R1R1R3 chain: 3-step rounds (R1, R1, R3)
theorem r1r1r3_chain : ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
  have many_step : ∀ k, ∀ c d e, ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _); ring_nf; finish
  exact many_step k c d e

-- R3R2R2 drain: convert c to e (requires e >= 1)
theorem r3r2r2_drain : ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1⟩ := by
  have many_step : ∀ k, ∀ c e, ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1⟩ := by
    intro k; induction' k with k h <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step k c e

-- Even case: n = 2*m, transition (0,0,0,2*m+1,4*m+3) →⁺ (0,0,0,2*m+2,4*m+5)
theorem even_trans : ⟨0, 0, 0, 2*m+1, 4*m+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+2, 4*m+5⟩ := by
  -- Phase 1: R4 chain: (0,0,0,2m+1,4m+3) →* (0,2m+1,0,0,4m+3)
  rw [show (2*m+1 : ℕ) = 0 + (2*m+1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0))
  simp only [Nat.zero_add]
  -- Phase 2: R5 step: (0,2m+1,0,0,4m+3) → (2,2m+2,1,0,4m+2)
  rw [show (4*m+3 : ℕ) = (4*m+2) + 1 from by ring]
  step fm
  -- Phase 3: R1R1R3 chain with k=m+1 rounds
  rw [show (2*m+2 : ℕ) = 0 + 2*(m+1) from by ring,
      show (4*m+2 : ℕ) = (3*m+1) + (m+1) from by ring]
  apply stepStar_trans (r1r1r3_chain (b := 0))
  -- Now at: (2, 0, 1+(m+1), 0+2*(m+1), 3*m+1)
  -- Normalize and do R2,R2
  rw [show (1 + (m + 1) : ℕ) = m + 2 from by ring,
      show (0 + 2 * (m + 1) : ℕ) = 2*m+2 from by ring]
  step fm; step fm
  -- Phase 5: R3R2R2 drain: (0, 0, m+2, 2m+2, 3m+3)
  rw [show (m+2 : ℕ) = 0 + (m+2) from by ring,
      show (3*m+1+1+1 : ℕ) = (3*m+2) + 1 from by ring]
  apply stepStar_trans r3r2r2_drain
  ring_nf; finish

-- Odd case: n = 2*m+1, transition (0,0,0,2*m+2,4*m+5) →⁺ (0,0,0,2*m+3,4*m+7)
theorem odd_trans : ⟨0, 0, 0, 2*m+2, 4*m+5⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+3, 4*m+7⟩ := by
  -- Phase 1: R4 chain
  rw [show (2*m+2 : ℕ) = 0 + (2*m+2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0))
  simp only [Nat.zero_add]
  -- Phase 2: R5 step
  rw [show (4*m+5 : ℕ) = (4*m+4) + 1 from by ring]
  step fm
  -- Phase 3: R1R1R3 chain with k=m+1 rounds
  rw [show (2*m+3 : ℕ) = 1 + 2*(m+1) from by ring,
      show (4*m+4 : ℕ) = (3*m+3) + (m+1) from by ring]
  apply stepStar_trans (r1r1r3_chain (b := 1))
  -- Now at: (2, 1, 1+(m+1), 0+2*(m+1), 3m+3)
  -- Normalize and do R1,R2
  rw [show (1 + (m + 1) : ℕ) = m + 2 from by ring,
      show (0 + 2 * (m + 1) : ℕ) = 2*m+2 from by ring]
  step fm; step fm
  -- Phase 5: R3R2R2 drain
  rw [show (m+3 : ℕ) = 0 + (m+3) from by ring,
      show (3*m+3+1 : ℕ) = (3*m+3) + 1 from by ring]
  apply stepStar_trans r3r2r2_drain
  ring_nf; finish

-- Main transition: parameterized by n
theorem main_trans (n : ℕ) : ⟨0, 0, 0, n+1, 2*n+3⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, n+2, 2*n+5⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = 2m: need (0,0,0,2m+1,4m+3) →⁺ (0,0,0,2m+2,4m+5)
    subst hm
    rw [show m + m + 1 = 2*m+1 from by ring,
        show 2 * (m + m) + 3 = 4*m+3 from by ring,
        show m + m + 2 = 2*m+2 from by ring,
        show 2 * (m + m) + 5 = 4*m+5 from by ring]
    exact even_trans
  · -- n = 2m+1: need (0,0,0,2m+2,4m+5) →⁺ (0,0,0,2m+3,4m+7)
    subst hm
    rw [show 2 * m + 1 + 1 = 2*m+2 from by ring,
        show 2 * (2 * m + 1) + 3 = 4*m+5 from by ring,
        show 2 * m + 1 + 2 = 2*m+3 from by ring,
        show 2 * (2 * m + 1) + 5 = 4*m+7 from by ring]
    exact odd_trans

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n+1, 2*n+3⟩) 0
  intro n; exists n+1; exact main_trans n

end Sz22_2003_unofficial_580
