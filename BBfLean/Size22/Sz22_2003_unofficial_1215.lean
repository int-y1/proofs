import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1215: [5/6, 539/2, 44/35, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  1
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1215

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move e to b
theorem e_to_b : ∀ k, ⟨(0 : ℕ), b, 0, D, e + k⟩ [fm]⊢* ⟨0, b + k, 0, D, e⟩ := by
  intro k; induction' k with k ih generalizing b D e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R3+R1+R1 chain: f rounds
theorem r3r1r1_chain : ∀ f, ⟨(0 : ℕ), B + 2 * f, 1, d + f, (0 : ℕ)⟩ [fm]⊢*
    ⟨0, B, f + 1, d, f⟩ := by
  intro f; induction' f with f ih generalizing B d
  · exists 0
  · rw [show B + 2 * (f + 1) = (B + 2) + 2 * f from by ring,
        show d + (f + 1) = (d + 1) + f from by ring]
    apply stepStar_trans (ih (B := B + 2) (d := d + 1))
    step fm; step fm; step fm
    rw [show f + 2 = (f + 1) + 1 from by ring]
    finish

-- R3+R2+R2 chain: C rounds
theorem r3r2r2_chain : ∀ C, ⟨(0 : ℕ), (0 : ℕ), C, d + 1, E⟩ [fm]⊢*
    ⟨0, 0, 0, d + 1 + 3 * C, E + 3 * C⟩ := by
  intro C; induction' C with C ih generalizing d E
  · simp; exists 0
  · rw [show (C + 1 : ℕ) = C + 1 from rfl]
    step fm; step fm; step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 3) (E := E + 3))
    ring_nf; finish

-- Main transition: (0, 0, 0, f+2+g, 2f+1) ->+ (0, 0, 0, 3f+5+g, 4f+5)
-- Here D = f+2+g, so D >= f+2.
theorem main_transition (f g : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, f + 2 + g, 2 * f + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 3 * f + 5 + g, 4 * f + 5⟩ := by
  -- Phase 1: move e=2f+1 to b via R4
  rw [show 2 * f + 1 = 0 + (2 * f + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * f + 1) (b := 0) (D := f + 2 + g) (e := 0))
  rw [show (0 : ℕ) + (2 * f + 1) = 1 + 2 * f from by ring]
  -- State: (0, 1+2f, 0, f+2+g, 0)
  -- Phase 2: R5 step
  rw [show f + 2 + g = (f + 1 + g) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 1 + 2 * f, 0, (f + 1 + g) + 1, 0⟩ : Q) [fm]⊢ ⟨0, 1 + 2 * f, 1, f + 1 + g, 0⟩)
  -- State: (0, 1+2f, 1, f+1+g, 0)
  -- Phase 3: R3+R1+R1 chain, f rounds
  rw [show f + 1 + g = (g + 1) + f from by ring]
  apply stepStar_trans (r3r1r1_chain f (B := 1) (d := g + 1))
  -- State: (0, 1, f+1, g+1, f)
  -- Phase 4: R3 + R1 + R2
  rw [show g + 1 = g + 1 from rfl]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, 1, f + 1, g + 1, f⟩ : Q) [fm]⊢ ⟨2, 1, f, g, f + 1⟩))
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨2, 1, f, g, f + 1⟩ : Q) [fm]⊢ ⟨1, 0, f + 1, g, f + 1⟩))
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, 0, f + 1, g, f + 1⟩ : Q) [fm]⊢ ⟨0, 0, f + 1, g + 2, f + 2⟩))
  -- State: (0, 0, f+1, g+2, f+2)
  -- Phase 5: R3+R2+R2 chain, f+1 rounds
  rw [show g + 2 = (g + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (f + 1) (d := g + 1) (E := f + 2))
  rw [show g + 1 + 1 + 3 * (f + 1) = 3 * f + 5 + g from by ring,
      show f + 2 + 3 * (f + 1) = 4 * f + 5 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ f g, q = ⟨0, 0, 0, f + 2 + g, 2 * f + 1⟩)
  · intro c ⟨f, g, hq⟩; subst hq
    refine ⟨⟨0, 0, 0, 3 * f + 5 + g, 4 * f + 5⟩,
      ⟨2 * f + 2, g + f + 1, ?_⟩, main_transition f g⟩
    ring_nf
  · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_1215
