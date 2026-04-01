import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1152: [5/6, 44/35, 637/2, 9/11, 5/13]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  0
-1  0  0  2  0  1
 0  2  0  0 -1  0
 0  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1152

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+2, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R3 drain: (A, 0, 0, d, e, f) →* (0, 0, 0, d + 2*A, e, f + A)
theorem r3_drain : ∀ A d e f, ⟨A, 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * A, e, f + A⟩ := by
  intro A; induction' A with A ih <;> intro d e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 2) e (f + 1))
    ring_nf; finish

-- R4 drain: (0, b, 0, d, E, f) →* (0, b + 2*E, 0, d, 0, f)
theorem r4_drain : ∀ E b d f, ⟨0, b, 0, d, E, f⟩ [fm]⊢* ⟨0, b + 2 * E, 0, d, 0, f⟩ := by
  intro E; induction' E with E ih <;> intro b d f
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 2) d f)
    ring_nf; finish

-- R2-R1-R1 chain: j 3-step rounds
theorem r2r1r1_chain : ∀ j c D E F,
    ⟨0, 2 * j, c + 1, D + j, E, F⟩ [fm]⊢* ⟨0, 0, c + j + 1, D, E + j, F⟩ := by
  intro j; induction' j with j ih <;> intro c D E F
  · exists 0
  · rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring,
        show D + (j + 1) = (D + j) + 1 from by ring]
    step fm
    rw [show 2 * j + 1 = (2 * j) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (c + 1) D (E + 1) F)
    ring_nf; finish

-- R2 chain (b=0)
theorem r2_chain : ∀ C a D E F, ⟨a, 0, C, D + C, E, F⟩ [fm]⊢* ⟨a + 2 * C, 0, 0, D, E + C, F⟩ := by
  intro C; induction' C with C ih <;> intro a D E F
  · exists 0
  · rw [show D + (C + 1) = (D + C) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) D (E + 1) F)
    ring_nf; finish

-- R5 + R2R1R1 + R2: combined phase
-- Start: (0, 2*E, 0, D₀+2*E+1, 0, F+1)
-- R5: (0, 2*E, 1, D₀+2*E+1, 0, F)
-- R2R1R1 (E rounds): (0, 0, E+1, D₀+E+1, E, F)
-- R2 (E+1 steps): (2*E+2, 0, 0, D₀, 2*E+1, F)
theorem r5_chain (E D₀ F : ℕ) :
    ⟨0, 2 * E, 0, D₀ + 2 * E + 1, 0, F + 1⟩ [fm]⊢⁺ ⟨2 * E + 2, 0, 0, D₀, 2 * E + 1, F⟩ := by
  step fm
  -- R2R1R1 chain (E rounds)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show D₀ + 2 * E + 1 = (D₀ + E + 1) + E from by ring]
  apply stepStar_trans (r2r1r1_chain E 0 (D₀ + E + 1) 0 F)
  -- After: (0, 0, E+1, D₀+E+1, E, F)
  rw [show 0 + E + 1 = E + 1 from by ring,
      show 0 + E = E from by ring,
      show D₀ + E + 1 = D₀ + (E + 1) from by ring]
  -- R2 chain (E+1 steps)
  apply stepStar_trans (r2_chain (E + 1) 0 D₀ E F)
  rw [show 0 + 2 * (E + 1) = 2 * E + 2 from by ring,
      show E + (E + 1) = 2 * E + 1 from by ring]
  finish

-- Main transition
theorem main_transition (d g : ℕ) :
    ⟨d + g + 1, 0, 0, d, d + g, g⟩ [fm]⊢⁺ ⟨2 * d + 2 * g + 2, 0, 0, d + 1, 2 * d + 2 * g + 1, d + 2 * g⟩ := by
  -- Phases 1-2: R3 + R4
  apply stepStar_stepPlus_stepPlus (r3_drain (d + g + 1) d (d + g) g)
  rw [show d + 2 * (d + g + 1) = 3 * d + 2 * g + 2 from by ring,
      show g + (d + g + 1) = (d + 2 * g) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus
  · have h := r4_drain (d + g) 0 (3 * d + 2 * g + 2) ((d + 2 * g) + 1)
    rw [show 0 + 2 * (d + g) = 2 * (d + g) from by ring] at h
    exact h
  -- After R4: (0, 2*(d+g), 0, 3*d+2*g+2, 0, (d+2*g)+1)
  -- Phases 3-5: R5 + R2R1R1 + R2
  rw [show 3 * d + 2 * g + 2 = (d + 1) + 2 * (d + g) + 1 from by ring]
  have h := r5_chain (d + g) (d + 1) (d + 2 * g)
  rw [show 2 * (d + g) + 2 = 2 * d + 2 * g + 2 from by ring,
      show 2 * (d + g) + 1 = 2 * d + 2 * g + 1 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 2, 3, 1⟩)
  · execute fm 12
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, g⟩ ↦ ⟨d + g + 1, 0, 0, d, d + g, g⟩) ⟨2, 1⟩
  intro ⟨d, g⟩
  refine ⟨⟨d + 1, d + 2 * g⟩, ?_⟩
  show ⟨d + g + 1, 0, 0, d, d + g, g⟩ [fm]⊢⁺ ⟨(d + 1) + (d + 2 * g) + 1, 0, 0, d + 1, (d + 1) + (d + 2 * g), d + 2 * g⟩
  rw [show (d + 1) + (d + 2 * g) + 1 = 2 * d + 2 * g + 2 from by ring,
      show (d + 1) + (d + 2 * g) = 2 * d + 2 * g + 1 from by ring]
  exact main_transition d g

end Sz22_2003_unofficial_1152
