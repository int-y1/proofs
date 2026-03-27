import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #575: [35/6, 11/2, 4/55, 3/7, 24/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 3  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_575

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+3, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R3+R2+R2 drain: convert c to e (with b=0)
theorem r3r2r2_drain : ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
  have many_step : ∀ k c e, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
    intro k; induction' k with k h <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + k + 1 + 1 = (e + 2) + k from by ring]
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c e

-- Interleave: R3+R1+R1 chain consuming pairs of b
theorem interleave_chain : ∀ k, ∀ b c d e,
    ⟨0, b+2*k, c+1, d, e+k⟩ [fm]⊢* ⟨0, b, c+1+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro b c d e
  · simp; exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Single b=1 drain: R3+R1+R2
theorem b1_drain : ⟨0, 1, c+1, d, e+1⟩ [fm]⊢* ⟨0, 0, c+1, d+1, e+1⟩ := by
  step fm; step fm; step fm; finish

-- Full transition for even n: n = 2*m+2
theorem trans_even (m : ℕ) : ⟨0, 0, 0, 2*m+2, 2*(2*m+2)+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+3, 2*(2*m+3)+1⟩ := by
  -- Phase 1: d_to_b: (0,0,0,2m+2,4m+5) -> (0,2m+2,0,0,4m+5)
  rw [show 2*(2*m+2)+1 = 4*m+5 from by ring, show 2*m+2 = 0+(2*m+2) from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  simp only [Nat.zero_add]
  -- Phase 2: R5: (0,2m+2,0,0,4m+5) -> (3,2m+3,0,0,4m+4)
  rw [show 4*m+5 = (4*m+4)+1 from by ring]
  step fm
  -- Phase 3: R1 x 3: (3,2m+3,0,0,4m+4) -> (0,2m,3,3,4m+4)
  rw [show (2*m+2)+1 = (2*m)+3 from by ring]
  step fm; step fm; step fm
  -- Phase 4: interleave: (0, 2m, 3, 3, 4m+4) -> (0, 0, 3+m, 3+2m, 4m+4-m)
  -- We need: (0, 0+2*m, 2+1, 3, (3*m+4)+m) ->* (0, 0, 2+1+m, 3+2*m, 3*m+4)
  rw [show 4*m+4 = (3*m+4)+m from by ring, show (2*m : ℕ) = 0+2*m from by ring,
      show (3 : ℕ) = 2+1 from by ring]
  apply stepStar_trans (interleave_chain m 0 2 3 (3*m+4))
  simp only [Nat.zero_add]
  -- Now at (0, 0, 3+m, 3+2*m, 3*m+4)
  -- Phase 5: drain: (0, 0, 3+m, 3+2*m, 3*m+4) -> (0, 0, 0, 3+2*m, 3*m+4+3+m)
  -- = (0, 0, 0, 2m+3, 4m+7) = (0, 0, 0, 2m+3, 2*(2m+3)+1) ✓
  rw [show 3+m = 0+(3+m) from by ring, show 3*m+4 = (2*m+1)+(3+m) from by ring]
  apply stepStar_trans (r3r2r2_drain (k := 3+m) (c := 0) (d := 3+2*m) (e := 2*m+1))
  ring_nf; finish

-- Full transition for odd n: n = 2*m+3
theorem trans_odd (m : ℕ) : ⟨0, 0, 0, 2*m+3, 2*(2*m+3)+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+4, 2*(2*m+4)+1⟩ := by
  -- Phase 1: d_to_b: (0,0,0,2m+3,4m+7) -> (0,2m+3,0,0,4m+7)
  rw [show 2*(2*m+3)+1 = 4*m+7 from by ring, show 2*m+3 = 0+(2*m+3) from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  simp only [Nat.zero_add]
  -- Phase 2: R5: (0,2m+3,0,0,4m+7) -> (3,2m+4,0,0,4m+6)
  rw [show 4*m+7 = (4*m+6)+1 from by ring]
  step fm
  -- Phase 3: R1 x 3: (3,2m+4,0,0,4m+6) -> (0,2m+1,3,3,4m+6)
  rw [show (2*m+3)+1 = (2*m+1)+3 from by ring]
  step fm; step fm; step fm
  -- Phase 4: interleave: (0, 2m+1, 3, 3, 4m+6)
  -- Need to handle odd b = 2m+1 = 1 + 2*m
  -- (0, 1+2*m, 2+1, 3, (3*m+6)+m) ->* (0, 1, 2+1+m, 3+2*m, 3*m+6)
  rw [show (2*m+1 : ℕ) = 1+2*m from by ring, show (3 : ℕ) = 2+1 from by ring,
      show 4*m+6 = (3*m+6)+m from by ring]
  apply stepStar_trans (interleave_chain m 1 2 3 (3*m+6))
  -- Now at (0, 1, 3+m, 3+2*m, 3*m+6)
  -- Phase 5: b1_drain: (0, 1, 3+m, 3+2*m, 3*m+6) -> (0, 0, 3+m, 4+2*m, 3*m+6)
  rw [show 3+m = (2+m)+1 from by ring, show 3*m+6 = (3*m+5)+1 from by ring]
  apply stepStar_trans b1_drain
  -- Now at (0, 0, 3+m, 4+2*m, 3*m+6)
  -- Phase 6: drain: (0, 0, 3+m, 4+2*m, 3*m+6) -> (0, 0, 0, 4+2*m, 3*m+6+3+m)
  -- = (0, 0, 0, 2m+4, 4m+9) = (0, 0, 0, 2m+4, 2*(2m+4)+1) ✓
  rw [show (2+m)+1 = 0+(3+m) from by ring,
      show (3*m+5)+1 = (2*m+3)+(3+m) from by ring,
      show 3+2*m+1 = 4+2*m from by ring]
  apply stepStar_trans (r3r2r2_drain (k := 3+m) (c := 0) (d := 4+2*m) (e := 2*m+3))
  ring_nf; finish

-- Combine even and odd transitions
theorem main_trans (n : ℕ) : ⟨0, 0, 0, n+2, 2*(n+2)+1⟩ [fm]⊢⁺ ⟨0, 0, 0, n+3, 2*(n+3)+1⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m + 2 = 2*m+2 from by ring, show m + m + 3 = 2*m+3 from by ring]
    exact trans_even m
  · subst hm
    rw [show 2 * m + 1 + 2 = 2*m+3 from by ring, show 2 * m + 1 + 3 = 2*m+4 from by ring]
    exact trans_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 5⟩) (by execute fm 19)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n+2, 2*(n+2)+1⟩) 0
  intro n; exists n+1; exact main_trans n

end Sz22_2003_unofficial_575
