import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1259: [5/6, 77/2, 8/35, 9/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 3  0 -1 -1  0
 0  2  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1259

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: drain d, accumulate into b
theorem r4_drain : ∀ k b d e, ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih
  · intro b d e; simp; exists 0
  · intro b d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

-- One subA round: 6 steps taking (0, b+4, c, 0, e+1) to (0, b, c+3, 0, e)
-- We prove this for concrete c (no symbolic c+3*k in the state)
theorem subA_one_round : ∀ b c e, ⟨(0 : ℕ), b + 4, c, 0, e + 1⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 3, 0, e⟩ := by
  intro b c e
  step fm  -- R5: (1, b+4, c, 1, e)
  step fm  -- R1: (0, b+3, c+1, 1, e)
  step fm  -- R3: (3, b+3, c, 0, e)
  step fm  -- R1: (2, b+2, c+1, 0, e)
  step fm  -- R1: (1, b+1, c+2, 0, e)
  step fm  -- R1: (0, b, c+3, 0, e)
  finish

-- SubA chain of k rounds: (0, 4k, c, 0, e+k) ->* (0, 0, c+3k, 0, e)
theorem subA_chain : ∀ k c e, ⟨(0 : ℕ), 4 * k, c, 0, e + k⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c e; simp; exists 0
  · intro c e
    rw [show 4 * (k + 1) = (4 * k) + 4 from by ring]
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans (subA_one_round (4 * k) c (e + k))
    apply stepStar_trans (ih (c + 3) e)
    rw [show c + 3 + 3 * k = c + 3 * (k + 1) from by ring]
    finish

-- R3+R2+R2+R2 chain: each round reduces c by 1, adds 2 to d, adds 3 to e
theorem r3r2r2r2_chain : ∀ k c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + 2 * k + 1, e + 3 * k⟩ := by
  intro k; induction' k with k ih
  · intro c d e; simp; exists 0
  · intro c d e
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e)
    rw [show d + 2 * k + 1 = (d + 2 * k) + 1 from by ring]
    step fm  -- R3: (3, 0, c, d+2k, e+3k)
    step fm  -- R2: (2, 0, c, d+2k+1, e+3k+1)
    step fm  -- R2: (1, 0, c, d+2k+2, e+3k+2)
    step fm  -- R2: (0, 0, c, d+2k+3, e+3k+3)
    rw [show d + 2 * k + 3 = d + 2 * (k + 1) + 1 from by ring,
        show e + 3 * k + 3 = e + 3 * (k + 1) from by ring]
    finish

-- Main transition: (0, 0, 0, 2*(k+2), E+k+3) ⊢⁺ (0, 0, 0, 2*(3k+7), E+9k+19)
theorem main_transition (k E : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, 2 * (k + 2), E + k + 3⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 2 * (3 * k + 7), E + 9 * k + 19⟩ := by
  -- Phase 1: R4 drain all d into b
  rw [show 2 * (k + 2) = 0 + 2 * (k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (2 * (k + 2)) 0 0 (E + k + 3))
  -- State: (0, 4*(k+2), 0, 0, E+k+3)
  rw [show (0 : ℕ) + 2 * (2 * (k + 2)) = 4 * (k + 2) from by ring,
      show E + k + 3 = (E + 1) + (k + 2) from by ring]
  -- Phase 2: SubA chain, k+2 rounds
  apply stepStar_stepPlus_stepPlus (subA_chain (k + 2) 0 (E + 1))
  rw [show (0 : ℕ) + 3 * (k + 2) = 3 * k + 6 from by ring]
  -- State: (0, 0, 3k+6, 0, E+1)
  -- Phase 3: SubB entry (R5 + R2, 2 steps)
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0, 3 * k + 6, 0, E + 1⟩ : Q) [fm]⊢ ⟨1, 0, 3 * k + 6, 1, E⟩)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, 0, 3 * k + 6, 1, E⟩ : Q) [fm]⊢ ⟨0, 0, 3 * k + 6, 2, E + 1⟩))
  -- State: (0, 0, 3k+6, 2, E+1)
  -- Phase 4: R3+R2*3 chain, 3k+6 rounds
  rw [show 3 * k + 6 = 0 + (3 * k + 6) from by ring,
      show 2 = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2r2_chain (3 * k + 6) 0 1 (E + 1))
  rw [show 1 + 2 * (3 * k + 6) + 1 = 2 * (3 * k + 7) from by ring,
      show E + 1 + 3 * (3 * k + 6) = E + 9 * k + 19 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 5⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, E⟩ ↦ ⟨0, 0, 0, 2 * (k + 2), E + k + 3⟩) ⟨0, 2⟩
  intro ⟨k, E⟩
  exists ⟨3 * k + 5, E + 6 * k + 11⟩
  show ⟨(0 : ℕ), (0 : ℕ), 0, 2 * (k + 2), E + k + 3⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), 0, 2 * ((3 * k + 5) + 2), (E + 6 * k + 11) + (3 * k + 5) + 3⟩
  have h := main_transition k E
  rw [show 2 * ((3 * k + 5) + 2) = 2 * (3 * k + 7) from by ring,
      show (E + 6 * k + 11) + (3 * k + 5) + 3 = E + 9 * k + 19 from by ring]
  exact h

end Sz22_2003_unofficial_1259
