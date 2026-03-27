import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #146: [1/45, 22/35, 845/2, 21/13, 5/33]

Vector representation:
```
 0 -2 -1  0  0  0
 1  0 -1 -1  1  0
-1  0  1  0  0  2
 0  1  0  1  0 -1
 0 -1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_146

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+2⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R2-R3 chain: each pair consumes 1 from d component, adds 1 to e and 2 to f
theorem r2r3_chain : ∀ j d e f,
    ⟨0, 1, 1, d+j, e, f⟩ [fm]⊢* ⟨(0:ℕ), 1, 1, d, e+j, f+2*j⟩ := by
  intro j; induction' j with j ih <;> intro d e f
  · exists 0
  rw [show d + (j + 1) = (d + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih d _ _)
  rw [show (e + 1) + j = e + (j + 1) from by ring,
      show (f + 2) + 2 * j = f + 2 * (j + 1) from by ring]
  finish

-- R4 chain: each step transfers 1 from f to b and d
theorem r4_chain : ∀ j b d e f,
    ⟨0, b, 0, d, e, f+j⟩ [fm]⊢* ⟨(0:ℕ), b+j, 0, d+j, e, f⟩ := by
  intro j; induction' j with j ih <;> intro b d e f
  · exists 0
  rw [show f + (j + 1) = (f + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  rw [show (b + 1) + j = b + (j + 1) from by ring,
      show (d + 1) + j = d + (j + 1) from by ring]
  finish

-- R5-R1 chain: each pair reduces b by 3 and e by 1
theorem r5r1_chain : ∀ j b d e,
    ⟨0, b+3*j, 0, d, e+j, 0⟩ [fm]⊢* ⟨(0:ℕ), b, 0, d, e, 0⟩ := by
  intro j; induction' j with j ih <;> intro b d e
  · exists 0
  rw [show b + 3 * (j + 1) = (b + 3 * j) + 3 from by ring,
      show e + (j + 1) = (e + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  finish

-- Main transition: (0, 2, 0, 3*E+3, E+1, 0) ->+ (0, 2, 0, 6*E+6, 2*E+2, 0)
theorem main_trans (E : ℕ) :
    ⟨0, 2, 0, 3*E+3, E+1, 0⟩ [fm]⊢⁺ ⟨(0:ℕ), 2, 0, 6*E+6, 2*E+2, 0⟩ := by
  -- Phase 1: R5 then R2-R3 chain
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2, 0, 3*E+3, E+1, 0⟩ = some ⟨0, 1, 1, 3*E+3, E, 0⟩
    simp only [fm]
  apply stepStar_trans
  · have h := r2r3_chain (3*E+3) 0 E 0
    rw [show 0 + (3*E+3) = 3*E+3 from by ring,
        show E + (3*E+3) = 4*E+3 from by ring,
        show 0 + 2*(3*E+3) = 6*E+6 from by ring] at h
    exact h
  -- Now at (0, 1, 1, 0, 4*E+3, 6*E+6)
  -- Phase 2: R4, R1
  step fm; step fm
  -- Now at (0, 0, 0, 1, 4*E+3, 6*E+5)
  -- Phase 3: R4 chain
  apply stepStar_trans
  · have h := r4_chain (6*E+5) 0 1 (4*E+3) 0
    rw [show 0 + (6*E+5) = 6*E+5 from by ring,
        show 1 + (6*E+5) = 6*E+6 from by ring] at h
    exact h
  -- Now at (0, 6*E+5, 0, 6*E+6, 4*E+3, 0)
  -- Phase 4: R5-R1 chain
  have h := r5r1_chain (2*E+1) 2 (6*E+6) (2*E+2)
  rw [show 2 + 3*(2*E+1) = 6*E+5 from by ring,
      show (2*E+2) + (2*E+1) = 4*E+3 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 3, 1, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2, 0, 3*n+3, n+1, 0⟩) 0
  intro n
  exact ⟨2*n+1, by
    have h := main_trans n
    rw [show 6*n+6 = 3*(2*n+1)+3 from by ring,
        show 2*n+2 = (2*n+1)+1 from by ring] at h
    exact h⟩

end Sz22_2003_unofficial_146
