import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #315: [154/15, 147/2, 1/3, 5/539, 22/7]

Vector representation:
```
 1 -1 -1  1  1
-1  1  0  2  0
 0 -1  0  0  0
 0  0  1 -2 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_315

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

/-- Phase 2: R2+R1 loop. (1, 0, k, d, e) →* (1, 0, 0, d+3*k, e+k) -/
theorem phase2 : ∀ k d e, ⟨1, 0, k, d, e⟩ [fm]⊢* (⟨1, 0, 0, d + 3 * k, e + k⟩ : Q) := by
  intro k; induction k with
  | zero => intro d e; exists 0
  | succ k ih =>
    intro d e
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

/-- Phase 4: R4 loop. (0, 0, c, d+2*k, k) →* (0, 0, c+k, d, 0) -/
theorem phase4 : ∀ k c d, ⟨0, 0, c, d + 2 * k, k⟩ [fm]⊢* (⟨0, 0, c + k, d, 0⟩ : Q) := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    show ⟨0, 0, c, d + 2 * k + 2, k + 1⟩ [fm]⊢* (⟨0, 0, c + k + 1, d, 0⟩ : Q)
    step fm
    show ⟨0, 0, c + 1, d + 2 * k, k⟩ [fm]⊢* (⟨0, 0, c + k + 1, d, 0⟩ : Q)
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

/-- Main transition: (0, 0, c+1, d+1, 0) →⁺ (0, 0, c+2, d+c+1, 0) -/
theorem main_trans (c d : ℕ) :
    (⟨0, 0, c + 1, d + 1, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, c + 2, d + c + 1, 0⟩ := by
  -- R5: (0,0,c+1,d+1,0) -> (1,0,c+1,d,1)
  step fm
  -- Phase 2: (1,0,c+1,d,1) ->* (1,0,0,d+3*(c+1),c+2)
  apply stepStar_trans (phase2 (c + 1) d 1)
  -- R2: (1,0,0,d+3c+3,c+2) -> (0,1,0,d+3c+5,c+2)
  step fm
  -- R3: (0,1,0,d+3c+5,c+2) -> (0,0,0,d+3c+5,c+2)
  step fm
  -- Phase 4: (0,0,0,d+3c+5,c+2) ->* (0,0,c+2,d+c+1,0)
  -- Need to show d+3*(c+1)+1 = (d+c+1) + 2*(c+2) and apply phase4
  show ⟨0, 0, 0, d + 3 * (c + 1) + 2, 1 + (c + 1)⟩ [fm]⊢* (⟨0, 0, c + 2, d + c + 1, 0⟩ : Q)
  rw [show d + 3 * (c + 1) + 2 = (d + c + 1) + 2 * (c + 2) from by ring,
      show 1 + (c + 1) = c + 2 from by ring]
  apply stepStar_trans (phase4 (c + 2) 0 (d + c + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨0, 0, 1, 1, 0⟩ : Q))
  · execute fm 6
  apply progress_nonhalt_simple (fm := fm)
    (C := fun p : ℕ × ℕ ↦ (⟨0, 0, p.1 + 1, p.2 + 1, 0⟩ : Q))
    (i₀ := ⟨0, 0⟩)
  intro ⟨c, d⟩
  exact ⟨⟨c + 1, d + c⟩, main_trans c d⟩
