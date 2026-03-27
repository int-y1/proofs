import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #621: [35/6, 1331/2, 4/55, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  3
 2  0 -1  0 -1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6

-/

namespace Sz22_2003_unofficial_621

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, n + k, e⟩ [fm]⊢* ⟨0, b + k, 0, n, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, n + k, e⟩ [fm]⊢* ⟨0, b + k, 0, n, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [show n + (k + 1) = (n + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R3R1R1 interleaved chain: each round B-=2, C+=1, D+=2, E-=1
theorem r3r1r1_chain : ⟨0, b + 2*k, c + 1, d, e + 1 + k⟩ [fm]⊢* ⟨0, b, c + 1 + k, d + 2*k, e + 1⟩ := by
  have many_step : ∀ k c d e, ⟨0, b + 2*k, c + 1, d, e + 1 + k⟩ [fm]⊢* ⟨0, b, c + 1 + k, d + 2*k, e + 1⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + 1 + (k + 1) = (e + 1 + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k c d e

-- R3R2R2 drain chain: each round C-=1, E+=5
theorem r3r2r2_drain : ⟨0, 0, c + k, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d, e + 6*k⟩ := by
  have many_step : ∀ k c e, ⟨0, 0, c + k, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d, e + 6*k⟩ := by
    intro k; induction' k with k h <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + k + 3 + 3 = (e + 6) + k from by ring]
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c e

-- Transition for n=0: (0,0,0,0,3) ->+ (0,0,0,1,5)
theorem trans_zero : ⟨0, 0, 0, 0, 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, 5⟩ := by
  execute fm 2

-- Transition for odd n = 2m+1 (m >= 0)
theorem trans_odd (m : ℕ) :
    ⟨0, 0, 0, 2*m+1, 4*m*m+6*m+5⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+2, 4*m*m+10*m+9⟩ := by
  -- Phase 1: R4 chain
  rw [show 2*m+1 = 0 + (2*m+1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (n := 0) (k := 2*m+1) (e := 4*m*m+6*m+5))
  rw [show 0 + (2*m+1) = 2*m+1 from by ring]
  -- Phase 2: R5+R1
  rw [show 2*m+1 = (2*m) + 1 from by ring,
      show 4*m*m+6*m+5 = (4*m*m+6*m+3) + 1 + 1 from by ring]
  step fm; step fm
  -- Phase 3: R3R1R1 chain (m rounds)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2*m = 0 + 2*m from by ring,
      show 4*m*m+6*m+3+1 = (4*m*m+5*m+3) + 1 + m from by ring]
  apply stepStar_trans (r3r1r1_chain (b := 0) (k := m) (c := 0) (d := 2) (e := 4*m*m+5*m+3))
  -- Phase 5: R3R2R2 drain (m+1 rounds)
  rw [show (0 : ℕ) + 1 + m = 0 + (m + 1) from by ring,
      show 2 + 2 * m = 2 * m + 2 from by ring,
      show 4*m*m+5*m+3+1 = (4*m*m+4*m+3) + (m+1) from by ring]
  apply stepStar_trans (r3r2r2_drain (d := 2*m+2) (k := m+1) (c := 0) (e := 4*m*m+4*m+3))
  ring_nf; finish

-- Transition for even n = 2m+2 (m >= 0)
theorem trans_even (m : ℕ) :
    ⟨0, 0, 0, 2*m+2, 4*m*m+10*m+9⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+3, 4*m*m+14*m+15⟩ := by
  -- Phase 1: R4 chain
  rw [show 2*m+2 = 0 + (2*m+2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (n := 0) (k := 2*m+2) (e := 4*m*m+10*m+9))
  rw [show 0 + (2*m+2) = 2*m+2 from by ring]
  -- Phase 2: R5+R1
  rw [show 2*m+2 = (2*m+1) + 1 from by ring,
      show 4*m*m+10*m+9 = (4*m*m+10*m+7) + 1 + 1 from by ring]
  step fm; step fm
  -- Phase 3: R3R1R1 chain (m rounds, b=1)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2*m+1 = 1 + 2*m from by ring,
      show 4*m*m+10*m+7+1 = (4*m*m+9*m+7) + 1 + m from by ring]
  apply stepStar_trans (r3r1r1_chain (b := 1) (k := m) (c := 0) (d := 2) (e := 4*m*m+9*m+7))
  -- Phase 4a: partial round R3,R1,R2
  rw [show (0 : ℕ) + 1 + m = m + 1 from by ring,
      show 2 + 2 * m = 2 * m + 2 from by ring,
      show 4*m*m+9*m+7+1 = (4*m*m+9*m+7) + 1 from by ring]
  step fm; step fm; step fm
  -- Phase 5: R3R2R2 drain (m+1 rounds)
  rw [show m + 1 = 0 + (m + 1) from by ring,
      show 4*m*m+9*m+10 = (4*m*m+8*m+9) + (m+1) from by ring]
  apply stepStar_trans (r3r2r2_drain (d := 2*m+3) (k := m+1) (c := 0) (e := 4*m*m+8*m+9))
  ring_nf; finish

-- Main transition combining all cases
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n, n*n+n+3⟩ [fm]⊢⁺ ⟨0, 0, 0, n+1, n*n+3*n+5⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = m + m
    subst hm
    rcases m with _ | m
    · -- n = 0
      exact trans_zero
    · -- n = (m+1)+(m+1) = 2m+2
      rw [show (m + 1) + (m + 1) = 2 * m + 2 from by ring,
          show (2*m+2)*(2*m+2)+(2*m+2)+3 = 4*m*m+10*m+9 from by ring,
          show (2*m+2)*(2*m+2)+3*(2*m+2)+5 = 4*m*m+14*m+15 from by ring,
          show (2*m+2)+1 = 2*m+3 from by ring]
      exact trans_even m
  · -- n = 2*m+1
    subst hm
    rw [show (2*m+1)*(2*m+1)+(2*m+1)+3 = 4*m*m+6*m+5 from by ring,
        show (2*m+1)*(2*m+1)+3*(2*m+1)+5 = 4*m*m+10*m+9 from by ring,
        show (2*m+1)+1 = 2*m+2 from by ring]
    exact trans_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 3⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n, n*n+n+3⟩) 0
  intro n; exists n+1
  rw [show (n+1)*(n+1)+(n+1)+3 = n*n+3*n+5 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_621
