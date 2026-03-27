import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #154: [1/45, 286/35, 55/2, 21/11, 5/39]

Vector representation:
```
 0 -2 -1  0  0  0
 1  0 -1 -1  1  1
-1  0  1  0  1  0
 0  1  0  1 -1  0
 0 -1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_154

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R4 chain: transfer e to b and d
theorem r4_chain : ∀ j, ∀ b d e f,
    ⟨0, b, 0, d, e+j, f⟩ [fm]⊢* ⟨0, b+j, 0, d+j, e, f⟩ := by
  intro j; induction' j with j ih <;> intro b d e f
  · exists 0
  rw [show e + (j + 1) = (e + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R5+R1 chain: each iteration does R5 then R1, net b-3 f-1
theorem r5r1_chain : ∀ j, ∀ b d f,
    ⟨0, b+3*j, 0, d, 0, f+j⟩ [fm]⊢* ⟨0, b, 0, d, 0, f⟩ := by
  intro j; induction' j with j ih <;> intro b d f
  · exists 0
  rw [show b + 3 * (j + 1) = (b + 3 * j) + 3 from by ring,
      show f + (j + 1) = (f + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3+R2 chain: consume d, grow e by 2 and f by 1 per iteration
theorem r3r2_chain : ∀ j, ∀ d e f,
    ⟨1, 0, 0, d+j, e, f⟩ [fm]⊢* ⟨1, 0, 0, d, e+2*j, f+j⟩ := by
  intro j; induction' j with j ih <;> intro d e f
  · exists 0
  rw [show d + (j + 1) = (d + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Main transition: canonical state with parameter k+1 (k >= 0, so parameter >= 1)
theorem main_trans (k : ℕ) :
    ⟨1, 0, 0, 0, 3*(k+1), 2*(k+1)⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 6*(k+1)+3, 4*(k+1)+2⟩ := by
  -- Preamble: 6 fixed steps via R3,R4,R2,R3,R4,R1
  apply stepStar_stepPlus_stepPlus
  · show ⟨1, 0, 0, 0, 3*(k+1), 2*(k+1)⟩ [fm]⊢* ⟨0, 0, 0, 1, 3*k+4, 2*k+3⟩
    step fm; step fm; step fm; step fm; step fm; step fm
    ring_nf; finish
  -- R4 chain: transfer e to b,d
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 0, 0, 1, 3*k+4, 2*k+3⟩ [fm]⊢* ⟨0, 3*k+4, 0, 3*k+5, 0, 2*k+3⟩
    have h := r4_chain (3*k+4) 0 1 0 (2*k+3)
    rw [show 0 + (3*k+4) = 3*k+4 from by ring,
        show 1 + (3*k+4) = 3*k+5 from by ring] at h
    exact h
  -- R5+R1 chain: consume b and f
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 3*k+4, 0, 3*k+5, 0, 2*k+3⟩ [fm]⊢* ⟨0, 1, 0, 3*k+5, 0, k+2⟩
    have h := r5r1_chain (k+1) 1 (3*k+5) (k+2)
    rw [show 1 + 3*(k+1) = 3*k+4 from by ring,
        show (k+2) + (k+1) = 2*k+3 from by ring] at h
    exact h
  -- R5: (0,1,0,3k+5,0,k+2) -> (0,0,1,3k+5,0,k+1)
  -- R2: (0,0,1,3k+5,0,k+1) -> (1,0,0,3k+4,1,k+2)
  -- Then R3+R2 chain: (1,0,0,3k+4,1,k+2) ->* (1,0,0,0,6k+9,4k+6)
  -- Total: 2 steps + chain, all positive
  step fm  -- R5
  step fm  -- R2
  step fm  -- first R3
  step fm  -- first R2
  -- Now we have a stepStar goal remaining with (3k+3) more R3+R2 pairs
  have h := r3r2_chain (3*k+3) 0 3 (k+3)
  rw [show 0 + (3*k+3) = 3*k+3 from by ring,
      show 3 + 2*(3*k+3) = 6*k+9 from by ring,
      show (k+3) + (3*k+3) = 4*k+6 from by ring] at h
  rw [show 6*(k+1)+3 = 6*k+9 from by ring,
      show 4*(k+1)+2 = 4*k+6 from by ring]
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 3, 2⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨1, 0, 0, 0, 3*(k+1), 2*(k+1)⟩) 0
  intro k
  exact ⟨2*k+2, by
    rw [show 3*(2*k+2+1) = 6*(k+1)+3 from by ring,
        show 2*(2*k+2+1) = 4*(k+1)+2 from by ring]
    exact main_trans k⟩

end Sz22_2003_unofficial_154
