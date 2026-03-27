import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #624: [35/6, 1331/2, 4/55, 3/7, 6/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  3
 2  0 -1  0 -1
 0  1  0 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_624

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 chain: convert d to b (requires a=0, c=0)
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R3R2R2 drain: each round converts one c, adding +5 to e
theorem drain : ∀ k c e, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d, e+6*k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = e + k + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + k + 3 + 3 = (e + 6) + k from by ring]
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Interleave chain: R3,R1,R1 rounds, each consuming 2 from b
theorem interleave_chain :
    ∀ k b c d e, ⟨0, b+2*k, c+1, d, e+k⟩ [fm]⊢* ⟨0, b, c+k+1, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro b c d e
  · exists 0
  rw [show b + 2 * (k + 1) = b + 2 * k + 2 from by ring,
      show e + (k + 1) = e + k + 1 from by ring]
  step fm
  rw [show b + 2 * k + 2 = (b + 2 * k + 1) + 1 from by ring]
  step fm
  rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
  step fm
  rw [show c + 2 = (c + 1) + 1 from by ring]
  apply stepStar_trans (h b (c+1) (d+2) e)
  ring_nf; finish

-- Even case: n = 2m
theorem even_trans (m : ℕ) :
    ⟨0, 0, 0, 2*m, 4*m*m+6*m+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+1, 4*m*m+10*m+7⟩ := by
  -- d_to_b: (0,0,0,2m,E) -> (0,2m,0,0,E)
  rw [show (2 : ℕ) * m = 0 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  simp only [Nat.zero_add]
  -- R5 + R1: (0,2m,0,0,E) -> (0,2m,1,1,E-1) in 2 steps
  rw [show 4*m*m+6*m+3 = (4*m*m+6*m+2) + 1 from by ring]
  step fm
  rw [show 2*m+1 = 2*m + 1 from by ring]
  step fm
  -- Now goal is ⊢* (from stepPlus_stepStar inside step fm)
  -- Interleave: m rounds (b=0)
  rw [show 4*m*m+6*m+2 = (4*m*m+5*m+2) + m from by ring]
  have ic := interleave_chain m 0 0 1 (4*m*m+5*m+2)
  simp only [Nat.zero_add] at ic
  apply stepStar_trans ic
  -- Now at: (0, 0, m+1, 1+2m, 4m^2+5m+2)
  -- Drain: (m+1) rounds
  rw [show m + 1 = 0 + (m + 1) from by ring,
      show 4*m*m+5*m+2 = (4*m*m+4*m+1) + (m + 1) from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring]
  apply stepStar_trans (drain (m + 1) 0 (4*m*m+4*m+1))
  ring_nf; finish

-- Odd case: n = 2m + 1
theorem odd_trans (m : ℕ) :
    ⟨0, 0, 0, 2*m+1, 4*m*m+10*m+7⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+2, 4*m*m+14*m+13⟩ := by
  -- d_to_b
  rw [show (2 : ℕ) * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  simp only [Nat.zero_add]
  -- R5 + R1
  rw [show 4*m*m+10*m+7 = (4*m*m+10*m+6) + 1 from by ring]
  step fm
  rw [show 2*m+1+1 = (2*m+1) + 1 from by ring]
  step fm
  -- Interleave: m rounds (b=1)
  rw [show (2 : ℕ) * m + 1 = 1 + 2 * m from by ring,
      show 4*m*m+10*m+6 = (4*m*m+9*m+6) + m from by ring]
  have ic := interleave_chain m 1 0 1 (4*m*m+9*m+6)
  simp only [Nat.zero_add] at ic
  apply stepStar_trans ic
  -- Now at: (0, 1, m+1, 1+2m, 4m^2+9m+6)
  rw [show 4*m*m+9*m+6 = (4*m*m+9*m+5) + 1 from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring]
  -- R3, R1, R2
  step fm
  rw [show (2 : ℕ) * m + 1 = (2 * m) + 1 from by ring]
  step fm; step fm
  -- Now at: (0, 0, m+1, 2m+2, 4m^2+9m+8)
  -- Drain: (m+1) rounds
  rw [show m + 1 = 0 + (m + 1) from by ring,
      show 4*m*m+9*m+8 = (4*m*m+8*m+7) + (m + 1) from by ring]
  apply stepStar_trans (drain (m + 1) 0 (4*m*m+8*m+7))
  ring_nf; finish

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n, n*n+3*n+3⟩ [fm]⊢⁺ ⟨0, 0, 0, n+1, (n+1)*(n+1)+3*(n+1)+3⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [hm, show (m + m) * (m + m) + 3 * (m + m) + 3 = 4*m*m+6*m+3 from by ring,
        show m + m + 1 = 2*m+1 from by ring,
        show (2*m+1)*(2*m+1)+3*(2*m+1)+3 = 4*m*m+10*m+7 from by ring,
        show m + m = 2 * m from by ring]
    exact even_trans m
  · rw [hm, show (2*m+1)*(2*m+1)+3*(2*m+1)+3 = 4*m*m+10*m+7 from by ring,
        show 2*m+1+1 = 2*m+2 from by ring,
        show (2*m+2)*(2*m+2)+3*(2*m+2)+3 = 4*m*m+14*m+13 from by ring]
    exact odd_trans m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 3⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n, n*n+3*n+3⟩) 0
  intro n; exists n+1; exact main_trans n

end Sz22_2003_unofficial_624
