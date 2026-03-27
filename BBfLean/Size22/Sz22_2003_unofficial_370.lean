import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #370: [2/15, 9/14, 1375/2, 7/11, 33/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  0
-1  0  3  0  1
 0  0  0  1 -1
 0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_370

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: convert e to d (when a=0, b=0)
theorem e_to_d : ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  have h : ∀ k d, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
    intro k; induction k with
    | zero => intro d; exists 0
    | succ k ih =>
      intro d
      rw [show e + (k + 1) = (e + k) + 1 from by ring]
      step fm
      apply stepStar_trans (ih _)
      ring_nf; finish
  exact h k d

-- R1 repeated: convert b,c to a
theorem r1_chain : ⟨a, b+k, c+k, d, e⟩ [fm]⊢* ⟨a+k, b, c, d, e⟩ := by
  have h : ∀ k a, ⟨a, b+k, c+k, d, e⟩ [fm]⊢* ⟨a+k, b, c, d, e⟩ := by
    intro k; induction k with
    | zero => intro a; exists 0
    | succ k ih =>
      intro a
      rw [show b + (k + 1) = (b + k) + 1 from by ring,
          show c + (k + 1) = (c + k) + 1 from by ring]
      step fm
      apply stepStar_trans (ih _)
      ring_nf; finish
  exact h k a

-- R3 repeated: convert a to c,e (when b=0, d=0)
theorem r3_chain : ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+3*k, 0, e+k⟩ := by
  have h : ∀ k c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+3*k, 0, e+k⟩ := by
    intro k; induction k with
    | zero => intro c e; exists 0
    | succ k ih =>
      intro c e
      rw [show a + (k + 1) = (a + k) + 1 from by ring]
      step fm
      apply stepStar_trans (ih _ _)
      ring_nf; finish
  exact h k c e

-- R2+R1x2 loop: each iteration does R2, R1, R1 in 3 steps
-- (a+1, 0, c+2, d+1, 1) -> (a, 2, c+2, d, 1) -> (a+1, 1, c+1, d, 1) -> (a+2, 0, c, d, 1)
-- Repeating k times:
theorem r2_r1_loop : ⟨a+1, 0, c+2+2*k, d+1+k, 1⟩ [fm]⊢* ⟨a+1+k, 0, c+2, d+1, 1⟩ := by
  have h : ∀ k a d, ⟨a+1, 0, c+2+2*k, d+1+k, 1⟩ [fm]⊢* ⟨a+1+k, 0, c+2, d+1, 1⟩ := by
    intro k; induction k with
    | zero => intro a d; exists 0
    | succ k ih =>
      intro a d
      rw [show c + 2 + 2 * (k + 1) = (c + 2 + 2 * k) + 1 + 1 from by ring,
          show d + 1 + (k + 1) = (d + 1 + k) + 1 from by ring,
          show a + 1 = (a + 1) from rfl]
      step fm; step fm; step fm
      apply stepStar_trans (ih _ _)
      ring_nf; finish
  exact h k a d

-- Full cycle step: from (0, 0, m²+9m+23, 0, 2m+9) to (0, 0, m²+11m+33, 0, 2m+11)
-- Using concrete coefficients to avoid Prod equality issues
theorem cycle_step (m : ℕ) :
    ⟨0, 0, m*m+9*m+23, 0, 2*m+9⟩ [fm]⊢⁺ ⟨0, 0, m*m+11*m+33, 0, 2*m+11⟩ := by
  -- Phase A: e_to_d (2m+9 steps)
  -- (0, 0, m²+9m+23, 0, 2m+9) -> (0, 0, m²+9m+23, 2m+9, 0)
  rw [show (2 : ℕ)*m+9 = 0 + (2*m+9) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_d (c := m*m+9*m+23) (d := 0) (e := 0))
  simp only [Nat.zero_add]
  -- Phase B: R5 + R1 (2 steps)
  -- (0, 0, m²+9m+23, 2m+9, 0) -> (1, 0, m²+9m+21, 2m+9, 1)
  rw [show m * m + 9 * m + 23 = (m * m + 9 * m + 21) + 1 + 1 from by ring]
  step fm; step fm
  -- Now at (1, 0, m²+9m+21, 2m+9, 1)
  -- Phase C: R2+R1x2 loop with k = 2m+8
  rw [show m * m + 9 * m + 21 = (m * m + 5 * m + 3) + 2 + 2 * (2 * m + 8) from by ring,
      show 2 * m + 9 = 0 + 1 + (2 * m + 8) from by ring]
  apply stepStar_trans (r2_r1_loop (a := 0) (c := m*m+5*m+3) (d := 0) (k := 2*m+8))
  -- Now at (2m+9, 0, m²+5m+5, 1, 1)
  -- One more R2+R1x2 step:
  rw [show (0 : ℕ) + 1 + (2 * m + 8) = (2 * m + 8) + 1 from by ring,
      show m * m + 5 * m + 3 + 2 = (m * m + 5 * m + 3) + 1 + 1 from by ring,
      show (0 : ℕ) + 1 = 1 from rfl]
  step fm; step fm; step fm
  -- Now at (2m+10, 0, m²+5m+3, 0, 1)
  -- Phase D: R3 chain (2m+10 steps)
  rw [show (2 : ℕ) * m + 8 + 1 + 1 = 0 + (2 * m + 10) from by ring]
  apply stepStar_trans (r3_chain (a := 0) (c := m*m+5*m+3) (e := 1) (k := 2*m+10))
  -- Goal: (0, 0, m*m+5*m+3+3*(2*m+10), 0, 1+2*m+10) ⊢* (0, 0, m*m+11*m+33, 0, 2*m+11)
  rw [show m * m + 5 * m + 3 + 3 * (2 * m + 10) = m * m + 11 * m + 33 from by ring,
      show 1 + (2 * m + 10) = 2 * m + 11 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 23, 0, 9⟩)
  · execute fm 93
  · -- (0, 0, 23, 0, 9) corresponds to m=0 in cycle_step
    -- since m²+9m+23 = 23, 2m+9 = 9 when m=0
    apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (C := fun n => ⟨0, 0, n*n+9*n+23, 0, 2*n+9⟩) (i₀ := 0)
    intro n
    use n + 1
    -- Need: (0, 0, n²+9n+23, 0, 2n+9) ⊢⁺ (0, 0, (n+1)²+9(n+1)+23, 0, 2(n+1)+9)
    -- = (0, 0, n²+11n+33, 0, 2n+11)
    have h1 : (n + 1) * (n + 1) + 9 * (n + 1) + 23 = n * n + 11 * n + 33 := by ring
    have h2 : 2 * (n + 1) + 9 = 2 * n + 11 := by ring
    rw [h1, h2]
    exact cycle_step n

end Sz22_2003_unofficial_370
