import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1740: [8/15, 33/14, 65/2, 7/11, 14/13]

Vector representation:
```
 3 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1740

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

-- R4 repeated: move e to d.
theorem e_to_d : ∀ k d, ⟨(0 : ℕ), 0, c, d, e + k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- R3 repeated: drain a, increase c and f.
theorem r3_drain : ∀ k c f, ⟨a + k, 0, c, (0 : ℕ), e, f⟩ [fm]⊢* ⟨a, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) (f + 1))
    ring_nf; finish

-- R2-R1 chain: interleaved d times.
theorem r2r1_chain : ∀ k c j, ⟨2 * j + 1, 0, c + k, k, j, f⟩ [fm]⊢* ⟨2 * (j + k) + 1, 0, c, 0, j + k, f⟩ := by
  intro k; induction' k with k ih <;> intro c j
  · exists 0
  · rw [show 2 * j + 1 = (2 * j) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    show ⟨2 * (j + 1) + 1, 0, c + k, k, j + 1, f⟩ [fm]⊢* _
    apply stepStar_trans (ih c (j + 1))
    ring_nf; finish

-- Main transition using offset parameters C, E, F.
-- Canonical state: (0, 0, C+E+2, 0, E+1, F+1)
-- Next state:      (0, 0, C+2E+5, 0, E+2, F+2E+5)
-- = (0, 0, (C+E+3)+(E+1)+2, 0, (E+1)+1, (F+2E+4)+1)
theorem main_trans_gen (E C F : ℕ) :
    ⟨0, 0, C + E + 2, 0, E + 1, F + 1⟩ [fm]⊢⁺
    ⟨0, 0, C + 2 * E + 5, 0, E + 2, F + 2 * E + 5⟩ := by
  -- Phase 1: R4 x (E+1)
  have phase1 : ⟨(0 : ℕ), 0, C + E + 2, 0, 0 + (E + 1), F + 1⟩ [fm]⊢*
      ⟨0, 0, C + E + 2, 0 + (E + 1), 0, F + 1⟩ :=
    e_to_d (E + 1) 0
  simp only [Nat.zero_add] at phase1
  apply stepStar_stepPlus_stepPlus phase1
  -- Phase 2: R5
  step fm
  -- Now at: (1, 0, C+E+2, E+2, 0, F)
  -- Phase 3: R2-R1 x (E+2)
  have phase3 : ⟨2 * 0 + 1, 0, C + (E + 2), E + 2, 0, F⟩ [fm]⊢*
      ⟨2 * (0 + (E + 2)) + 1, 0, C, 0, 0 + (E + 2), F⟩ :=
    r2r1_chain (E + 2) C 0
  simp only [Nat.zero_add] at phase3
  rw [show C + E + 2 = C + (E + 2) from by ring]
  apply stepStar_trans phase3
  -- Phase 4: R3 x (2E+5)
  have phase4 : ⟨0 + (2 * E + 5), 0, C, (0 : ℕ), E + 2, F⟩ [fm]⊢*
      ⟨0, 0, C + (2 * E + 5), 0, E + 2, F + (2 * E + 5)⟩ :=
    r3_drain (2 * E + 5) C F
  simp only [Nat.zero_add] at phase4
  rw [show 2 * (E + 2) + 1 = 2 * E + 5 from by ring]
  apply stepStar_trans phase4
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 1, 3⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨C, E, F⟩ ↦ ⟨0, 0, C + E + 2, 0, E + 1, F + 1⟩) ⟨1, 0, 2⟩
  intro ⟨C, E, F⟩
  refine ⟨⟨C + E + 2, E + 1, F + 2 * E + 4⟩, ?_⟩
  show ⟨0, 0, C + E + 2, 0, E + 1, F + 1⟩ [fm]⊢⁺
    ⟨0, 0, C + E + 2 + (E + 1) + 2, 0, E + 1 + 1, F + 2 * E + 4 + 1⟩
  have h := main_trans_gen E C F
  convert h using 2; ring_nf
