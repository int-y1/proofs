import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #94: [1/30, 21/2, 4/77, 5/7, 484/3]

Vector representation:
```
-1 -1 -1  0  0
-1  1  0  1  0
 2  0  0 -1 -1
 0  0  1 -1  0
 2 -1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_94

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | _ => none

-- [R2,R2,R3]^(E+1): (2, B, 0, D, E+1) →* (2, B+2*(E+1), 0, D+E+1, 0)
theorem r2r2r3_chain : ∀ E B D,
    ⟨2, B, 0, D, E + 1⟩ [fm]⊢* ⟨2, B + 2 * (E + 1), 0, D + E + 1, 0⟩ := by
  intro E; induction' E with E ih <;> intro B D
  · step fm; step fm; step fm; ring_nf; finish
  rw [show D + (E + 1) + 1 = (D + 1) + E + 1 from by ring,
      show B + 2 * (E + 1 + 1) = (B + 2) + 2 * (E + 1) from by ring]
  step fm; step fm; step fm
  exact ih _ _

-- R4^D: (0, B, C, D, 0) →* (0, B, C+D, 0, 0)
theorem r4_chain : ∀ D B C, ⟨0, B, C, D, 0⟩ [fm]⊢* ⟨0, B, C + D, 0, 0⟩ := by
  intro D; induction' D with D ih <;> intro B C
  · exists 0
  rw [show C + (D + 1) = (C + 1) + D from by ring]
  step fm
  exact ih _ _

-- [R5,R1,R1]^(k+1): (0, B+3*(k+1), 2*(k+1)+1, 0, E) →* (0, B, 1, 0, E+2*(k+1))
theorem r5r1r1_chain : ∀ k B E,
    ⟨0, B + 3 * (k + 1), 2 * (k + 1) + 1, 0, E⟩ [fm]⊢*
    ⟨0, B, 1, 0, E + 2 * (k + 1)⟩ := by
  intro k; induction' k with k ih <;> intro B E
  · rw [show B + 3 * 1 = (B + 2) + 1 from by ring,
        show 2 * 1 + 1 = 2 + 1 from by ring,
        show E + 2 * 1 = E + 2 from by ring]
    step fm
    rw [show (B + 2 : ℕ) = (B + 1) + 1 from by ring]
    step fm
    rw [show (B + 1 : ℕ) = B + 1 from rfl,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    finish
  rw [show B + 3 * (k + 1 + 1) = (B + 3) + 3 * (k + 1) from by ring,
      show 2 * (k + 1 + 1) + 1 = (2 * (k + 1) + 1 + 1) + 1 from by ring,
      show E + 2 * (k + 1 + 1) = (E + 2) + 2 * (k + 1) from by ring,
      show (B + 3) + 3 * (k + 1) = ((B + 2) + 3 * (k + 1)) + 1 from by ring]
  step fm
  rw [show ((B + 2) + 3 * (k + 1) : ℕ) = ((B + 1) + 3 * (k + 1)) + 1 from by ring]
  step fm
  rw [show ((B + 1) + 3 * (k + 1) : ℕ) = ((B + 3 * (k + 1)) : ℕ) + 1 from by ring,
      show (2 * (k + 1) + 1 + 1 : ℕ) = (2 * (k + 1) + 1) + 1 from by ring]
  step fm
  exact ih _ _

-- Main transition: (1, b, 0, 0, 2*(k+2)) →⁺ (1, b+k+1, 0, 0, 2*(k+3))
theorem main_transition (b k : ℕ) :
    ⟨1, b, 0, 0, 2 * (k + 2)⟩ [fm]⊢⁺ ⟨1, b + k + 1, 0, 0, 2 * (k + 3)⟩ := by
  -- P0: R2 then R3
  rw [show 2 * (k + 2) = (2 * k + 3) + 1 from by ring]
  step fm -- R2: -> (0, b+1, 0, 1, 2*k+3+1)
  step fm -- R3: -> (2, b+1, 0, 0, 2*k+3)
  -- Goal is ⊢* after two steps
  -- P1: [R2,R2,R3]^(2*k+3) chain. 2*k+3 = (2*k+2)+1
  rw [show (2 * k + 3 : ℕ) = (2 * k + 2) + 1 from by ring]
  apply stepStar_trans (r2r2r3_chain (2 * k + 2) (b + 1) 0)
  rw [show b + 1 + 2 * (2 * k + 2 + 1) = b + 4 * k + 7 from by ring,
      show (0 : ℕ) + (2 * k + 2) + 1 = 2 * k + 3 from by ring]
  -- P2: R2, R2: (2, b+4*k+7, 0, 2*k+3, 0) -> (0, b+4*k+9, 0, 2*k+5, 0)
  step fm; step fm
  rw [show b + 4 * k + 7 + 1 + 1 = b + 4 * k + 9 from by ring,
      show 2 * k + 3 + 1 + 1 = 2 * k + 5 from by ring]
  -- P3: R4 chain
  apply stepStar_trans (r4_chain (2 * k + 5) (b + 4 * k + 9) 0)
  rw [show (0 : ℕ) + (2 * k + 5) = 2 * (k + 2) + 1 from by ring,
      show b + 4 * k + 9 = (b + k + 3) + 3 * (k + 2) from by ring,
      show (k + 2 : ℕ) = (k + 1) + 1 from by ring]
  -- P4: [R5,R1,R1]^(k+2)
  apply stepStar_trans (r5r1r1_chain (k + 1) (b + k + 3) 0)
  rw [show (0 : ℕ) + 2 * (k + 1 + 1) = 2 * (k + 2) from by ring]
  -- State: (0, b+k+3, 1, 0, 2*(k+2))
  -- P5: R5 then R1
  rw [show (b + k + 3 : ℕ) = (b + k + 2) + 1 from by ring]
  step fm
  rw [show (b + k + 2 : ℕ) = (b + k + 1) + 1 from by ring,
      show 2 * (k + 2) + 2 = 2 * (k + 3) from by ring]
  step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 6⟩) (by execute fm 45)
  rw [show (6 : ℕ) = 2 * (1 + 2) from by ring]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨b, k⟩ ↦ ⟨1, b, 0, 0, 2 * (k + 2)⟩) ⟨0, 1⟩
  intro ⟨b, k⟩
  exact ⟨⟨b + k + 1, k + 1⟩, main_transition b k⟩

end Sz22_2003_unofficial_94
