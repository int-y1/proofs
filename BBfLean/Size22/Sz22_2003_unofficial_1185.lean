import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1185: [5/6, 49/2, 44/35, 9/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  2  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1185

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: drain e into b.
theorem r4_chain : ∀ k, ⟨0, b, 0, D, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, D, e⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 2) (e := e))
    ring_nf; finish

-- R3,R1,R1 chain.
theorem r3r1r1_chain : ∀ k, ⟨0, 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm  -- R3
    step fm  -- R1
    step fm  -- R1
    apply stepStar_trans (ih (c := c + 1) (d := d) (e := e + 1))
    ring_nf; finish

-- R3,R2,R2 chain (k rounds, keeping c >= 1 throughout).
theorem r3r2r2_chain : ∀ k, ⟨0, 0, c + k + 1, d + 1, e⟩ [fm]⊢* ⟨0, 0, c + 1, d + 3 * k + 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring]
    step fm  -- R3
    step fm  -- R2
    step fm  -- R2
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (c := c) (d := d + 3) (e := e + 1))
    ring_nf; finish

-- R3,R2,R2 last step: clear the final c=1.
theorem r3r2r2_last : ⟨0, 0, 1, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 4, e + 1⟩ := by
  step fm; step fm; step fm; finish

-- Phases 3+4: (0, 2*e, 1, e+1+e, 0) ⊢* (0, 0, 0, 4*e+4, 2*e+1)
theorem phases34 : ⟨0, 2 * e, 1, e + 1 + e, 0⟩ [fm]⊢* ⟨0, 0, 0, 4 * e + 4, 2 * e + 1⟩ := by
  -- Phase 3: R3,R1,R1 chain (e rounds)
  rw [show e + 1 + e = (e + 1) + e from by ring]
  apply stepStar_trans (r3r1r1_chain e (c := 0) (d := e + 1) (e := 0))
  -- State: (0, 0, 0+e+1, e+1, 0+e)
  -- Phase 4: R3,R2,R2 chain (e rounds) + last step
  show ⟨0, 0, 0 + e + 1, e + 1, 0 + e⟩ [fm]⊢* ⟨0, 0, 0, 4 * e + 4, 2 * e + 1⟩
  apply stepStar_trans (r3r2r2_chain e (c := 0) (d := e) (e := 0 + e))
  -- State: (0, 0, 0+1, e+3*e+1, 0+e+e)
  apply stepStar_trans (r3r2r2_last (d := e + 3 * e) (e := 0 + e + e))
  ring_nf; finish

-- Main transition: (0, 0, 0, 2*e+2, e) ⊢⁺ (0, 0, 0, 4*e+4, 2*e+1)
theorem main_trans : ⟨0, 0, 0, 2 * e + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * e + 4, 2 * e + 1⟩ := by
  -- Phase 1: R4 chain drains e to b
  rw [show (e : ℕ) = 0 + e from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain e (b := 0) (D := 2 * (0 + e) + 2) (e := 0))
  -- State: (0, 0+2*e, 0, 2*(0+e)+2, 0)
  rw [show (0 : ℕ) + 2 * e = 2 * e from by ring,
      show 2 * (0 + e) + 2 = 2 * e + 2 from by ring,
      show 4 * (0 + e) + 4 = 4 * e + 4 from by ring,
      show 2 * (0 + e) + 1 = 2 * e + 1 from by ring]
  -- Phase 2: R5 step. State: (0, 2*e, 0, 2*e+2, 0). R5: d=2*e+2=(2*e+1)+1.
  rw [show 2 * e + 2 = (e + 1 + e) + 1 from by ring]
  apply step_stepStar_stepPlus (by show (0, 2 * e, 0, (e + 1 + e) + 1, 0) [fm]⊢ (0, 2 * e, 1, e + 1 + e, 0); rfl)
  -- State: (0, 2*e, 1, e+1+e, 0). Now apply phases34.
  exact phases34

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨0, 0, 0, 2 * e + 2, e⟩) 0
  intro e; exists 2 * e + 1
  show ⟨0, 0, 0, 2 * e + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * (2 * e + 1) + 2, 2 * e + 1⟩
  rw [show 2 * (2 * e + 1) + 2 = 4 * e + 4 from by ring]
  exact main_trans

end Sz22_2003_unofficial_1185
