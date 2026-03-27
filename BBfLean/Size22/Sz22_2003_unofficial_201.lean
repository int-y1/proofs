import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #201: [1/6, 35/2, 182/55, 33/7, 4/39]

Vector representation:
```
-1 -1  0  0  0  0
-1  0  1  1  0  0
 1  0 -1  1 -1  1
 0  1  0 -1  1  0
 2 -1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_201

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+1, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | _ => none

-- R3-R2 loop: consume e, grow d and f
theorem r3r2_loop : ∀ k d f,
    ⟨0, 0, 2, d, k, f⟩ [fm]⊢* (⟨0, 0, 2, d + 2 * k, 0, f + k⟩ : Q) := by
  intro k; induction k with
  | zero => intro d f; exists 0
  | succ k ih =>
    intro d f
    rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    step fm; step fm
    exact ih (d + 2) (f + 1)

-- R4 repeated: drain d into b and e
theorem r4_repeat : ∀ k b e F,
    ⟨0, b, 0, k, e, F⟩ [fm]⊢* (⟨0, b + k, 0, 0, e + k, F⟩ : Q) := by
  intro k; induction k with
  | zero => intro b e F; exists 0
  | succ k ih =>
    intro b e F
    rw [show b + (k + 1) = (b + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    exact ih (b + 1) (e + 1) F

-- R5-R1-R1 drain: consume b by 3 and f by 1 each round
theorem r5r1r1_drain : ∀ k b E f,
    ⟨0, b + 3 * k, 0, 0, E, f + k⟩ [fm]⊢* (⟨0, b, 0, 0, E, f⟩ : Q) := by
  intro k; induction k with
  | zero => intro b E f; exists 0
  | succ k ih =>
    intro b E f
    rw [show b + 3 * (k + 1) = (b + 3 * k) + 1 + 1 + 1 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm; step fm
    exact ih b E f

-- Main transition: (2, 0, 0, 0, 3*f+1, f) ⊢⁺ (2, 0, 0, 0, 6*f+4, 2*f+1)
theorem main_trans (f : ℕ) :
    ⟨2, 0, 0, 0, 3 * f + 1, f⟩ [fm]⊢⁺ (⟨2, 0, 0, 0, 6 * f + 4, 2 * f + 1⟩ : Q) := by
  -- Phase 1: (2, 0, 0, 0, 3f+1, f) →* (0, 0, 2, 6f+4, 0, 4f+1)
  apply step_stepStar_stepPlus
  · show fm ⟨2, 0, 0, 0, 3 * f + 1, f⟩ = some ⟨1, 0, 1, 1, 3 * f + 1, f⟩; rfl
  apply stepStar_trans
  · show ⟨1, 0, 1, 1, 3 * f + 1, f⟩ [fm]⊢* (⟨0, 0, 2, 2, 3 * f + 1, f⟩ : Q)
    step fm; finish
  apply stepStar_trans
  · exact r3r2_loop (3 * f + 1) 2 f
  -- Now at (0, 0, 2, 6f+4, 0, 4f+1)
  -- Phase 2: tail cleanup
  rw [show 2 + 2 * (3 * f + 1) = (6 * f + 3) + 1 from by ring,
      show f + (3 * f + 1) = 4 * f + 1 from by ring]
  apply stepStar_trans
  · show ⟨0, 0, 2, (6 * f + 3) + 1, 0, 4 * f + 1⟩ [fm]⊢*
        (⟨0, 0, 0, (6 * f + 3) + 1, 0, (4 * f + 1) + 2⟩ : Q)
    step fm; step fm; step fm; step fm; step fm; step fm; finish
  -- Now at (0, 0, 0, 6f+4, 0, 4f+3)
  -- Phase 3: R4 drain
  rw [show (6 * f + 3) + 1 = 6 * f + 4 from by ring,
      show (4 * f + 1) + 2 = 4 * f + 3 from by ring]
  apply stepStar_trans
  · exact r4_repeat (6 * f + 4) 0 0 (4 * f + 3)
  -- Now at (0, 6f+4, 0, 0, 6f+4, 4f+3)
  rw [show 0 + (6 * f + 4) = 6 * f + 4 from by ring]
  -- Phase 4: R5-R1-R1 drain
  apply stepStar_trans (c₂ := (⟨0, 1, 0, 0, 6 * f + 4, 2 * f + 2⟩ : Q))
  · have h := r5r1r1_drain (2 * f + 1) 1 (6 * f + 4) (2 * f + 2)
    rw [show 1 + 3 * (2 * f + 1) = 6 * f + 4 from by ring,
        show (2 * f + 2) + (2 * f + 1) = 4 * f + 3 from by ring] at h
    exact h
  -- Final R5: (0, 1, 0, 0, 6f+4, 2f+2) → (2, 0, 0, 0, 6f+4, 2f+1)
  rw [show (2 * f + 2 : ℕ) = (2 * f + 1) + 1 from by ring]
  step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨2, 0, 0, 0, 1, 0⟩ : Q)) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ (⟨2, 0, 0, 0, 3 * n + 1, n⟩ : Q)) 0
  intro n
  exact ⟨2 * n + 1, by
    show (⟨2, 0, 0, 0, 3 * n + 1, n⟩ : Q) [fm]⊢⁺ ⟨2, 0, 0, 0, 3 * (2 * n + 1) + 1, 2 * n + 1⟩
    have h := main_trans n
    rw [show 6 * n + 4 = 3 * (2 * n + 1) + 1 from by ring] at h
    exact h⟩

end Sz22_2003_unofficial_201
