import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1996: [99/35, 5/6, 49/3, 4/11, 15/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  1  0  0
 0 -1  0  2  0
 2  0  0  0 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1996

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R1/R2 spiral: each pair does a-=1, b+=1, d-=1, e+=1, c stays at 1
theorem spiral : ∀ n, ∀ B D E, ⟨n, B, 1, D + n, E⟩ [fm]⊢* ⟨0, B + n, 1, D, E + n⟩ := by
  intro n; induction' n with n ih <;> intro B D E
  · exists 0
  · rw [show D + (n + 1) = (D + n) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (B := B + 1) (D := D) (E := E + 1))
    ring_nf; finish

-- R3 drain: move b to d (b to 0, d gains 2*b)
theorem b_drain : ∀ B, ⟨0, B, 0, D, E⟩ [fm]⊢* ⟨0, 0, 0, D + 2 * B, E⟩ := by
  intro B; induction' B with B ih generalizing D
  · exists 0
  · step fm
    apply stepStar_trans (ih (D := D + 2))
    ring_nf; finish

-- R4 drain: move e to a (e to 0, a gains 2*e)
theorem e_drain : ∀ E, ⟨A, 0, 0, D, E⟩ [fm]⊢* ⟨A + 2 * E, 0, 0, D, 0⟩ := by
  intro E; induction' E with E ih generalizing A
  · exists 0
  · step fm
    apply stepStar_trans (ih (A := A + 2))
    ring_nf; finish

-- Main transition: (2*(A+1), 0, 0, F+2*A+3, 0) →⁺ (2*(2*A+2), 0, 0, (F+4)+2*(2*A+1)+3, 0)
theorem main_trans : ∀ A F,
    ⟨2 * A + 2, 0, 0, F + 2 * A + 3, 0⟩ [fm]⊢⁺
    ⟨4 * A + 4, 0, 0, F + 4 * A + 9, 0⟩ := by
  intro A F
  step fm
  -- After R5: (2*A+1, 1, 1, F+2*A+3, 0)
  -- Need to show (2*A+1, 1, 1, F+2*A+3, 0) = (2*A+1, 1, 1, (F+2)+(2*A+1), 0)
  show ⟨2 * A + 1, 1, 1, F + 2 * A + 3, 0⟩ [fm]⊢* ⟨4 * A + 4, 0, 0, F + 4 * A + 9, 0⟩
  rw [show F + 2 * A + 3 = (F + 2) + (2 * A + 1) from by ring]
  apply stepStar_trans (spiral (2 * A + 1) (B := 1) (D := F + 2) (E := 0))
  -- After spiral: (0, 1+(2*A+1), 1, F+2, 0+(2*A+1)) = (0, 2*A+2, 1, F+2, 2*A+1)
  rw [show 1 + (2 * A + 1) = 2 * A + 2 from by ring,
      show 0 + (2 * A + 1) = 2 * A + 1 from by ring,
      show F + 2 = (F + 1) + 1 from by ring]
  step fm
  -- After R1: (0, 2*A+4, 0, F+1, 2*A+2)
  show ⟨0, 2 * A + 4, 0, F + 1, 2 * A + 2⟩ [fm]⊢* ⟨4 * A + 4, 0, 0, F + 4 * A + 9, 0⟩
  apply stepStar_trans (b_drain (2 * A + 4) (D := F + 1) (E := 2 * A + 2))
  -- After b_drain: (0, 0, 0, F+1+2*(2*A+4), 2*A+2) = (0, 0, 0, F+4*A+9, 2*A+2)
  rw [show F + 1 + 2 * (2 * A + 4) = F + 4 * A + 9 from by ring]
  apply stepStar_trans (e_drain (2 * A + 2) (A := 0) (D := F + 4 * A + 9))
  -- After e_drain: (0+2*(2*A+2), 0, 0, F+4*A+9, 0) = (4*A+4, 0, 0, F+4*A+9, 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 5, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, F⟩ ↦ ⟨2 * A + 2, 0, 0, F + 2 * A + 3, 0⟩) ⟨0, 2⟩
  intro ⟨A, F⟩
  exact ⟨⟨2 * A + 1, F + 4⟩, by
    show ⟨2 * A + 2, 0, 0, F + 2 * A + 3, 0⟩ [fm]⊢⁺
         ⟨2 * (2 * A + 1) + 2, 0, 0, (F + 4) + 2 * (2 * A + 1) + 3, 0⟩
    rw [show 2 * (2 * A + 1) + 2 = 4 * A + 4 from by ring,
        show (F + 4) + 2 * (2 * A + 1) + 3 = F + 4 * A + 9 from by ring]
    exact main_trans A F⟩
