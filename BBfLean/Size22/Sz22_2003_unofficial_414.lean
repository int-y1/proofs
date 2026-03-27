import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #414: [25/63, 28/3, 3/10, 11/2, 9/11]

Vector representation:
```
 0 -2  2 -1  0
 2 -1  0  1  0
-1  1 -1  0  0
-1  0  0  0  1
 0  2  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_414

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- Phase 1: R5,R1 loop. Each iteration: (0,0,c,d'+1,e'+1) ->* (0,0,c+2,d',e')
theorem phase1_one : ∀ c d e,
    ⟨0, 0, c, d+1, e+1⟩ [fm]⊢* ⟨0, 0, c+2, d, e⟩ := by
  intro c d e; step fm; step fm; finish

theorem phase1 : ∀ j c d e,
    ⟨0, 0, c, d+j, e+j⟩ [fm]⊢* ⟨0, 0, c+2*j, d, e⟩ := by
  intro j; induction j with
  | zero => intro c d e; exists 0
  | succ j ih =>
    intro c d e
    rw [show d + (j + 1) = (d + j) + 1 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    apply stepStar_trans (phase1_one _ _ _)
    apply stepStar_trans (ih _ _ _)
    rw [show (c + 2) + 2 * j = c + 2 * (j + 1) from by ring]
    finish

-- Phase 2+3: R5,R2,R2: (0,0,2d,0,r+1) -> (4,0,2d,2,r)
theorem phase23 : ∀ c r,
    ⟨0, 0, c, 0, r+1⟩ [fm]⊢* ⟨4, 0, c, 2, r⟩ := by
  intro c r; step fm; step fm; step fm; finish

-- Phase 4: R3,R2 loop. Each iteration: (a+1,0,c+1,d,e) -> (a+2,0,c,d+1,e)
theorem phase4_one : ∀ a c d e,
    ⟨a+1, 0, c+1, d, e⟩ [fm]⊢* ⟨a+2, 0, c, d+1, e⟩ := by
  intro a c d e; step fm; step fm; ring_nf; finish

theorem phase4 : ∀ j a c d e,
    ⟨a+1, 0, c+j, d, e⟩ [fm]⊢* ⟨a+1+j, 0, c, d+j, e⟩ := by
  intro j; induction j with
  | zero => intro a c d e; exists 0
  | succ j ih =>
    intro a c d e
    rw [show c + (j + 1) = (c + j) + 1 from by ring]
    apply stepStar_trans (phase4_one _ _ _ _)
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- Phase 5: R4 loop. Each iteration: (a+1,0,0,d,e) -> (a,0,0,d,e+1)
theorem phase5 : ∀ j a d e,
    ⟨a+j, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+j⟩ := by
  intro j; induction j with
  | zero => intro a d e; exists 0
  | succ j ih =>
    intro a d e
    rw [show a + (j + 1) = (a + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    rw [show (e + 1) + j = e + (j + 1) from by ring]
    finish

-- Combined phases 4+5: (4,0,2d,2,r) ->* (0,0,0,2d+2,2d+r+4)
theorem phase45 (d r : ℕ) :
    ⟨4, 0, 2*d, 2, r⟩ [fm]⊢* ⟨0, 0, 0, 2*d+2, 2*d+r+4⟩ := by
  apply stepStar_trans
  · have h := phase4 (2*d) 3 0 2 r
    rw [show 3 + 1 = 4 from by ring,
        show 0 + 2 * d = 2 * d from by ring,
        show 3 + 1 + 2 * d = 2 * d + 4 from by ring,
        show 2 + 2 * d = 2 * d + 2 from by ring] at h
    exact h
  have h := phase5 (2*d+4) 0 (2*d+2) r
  rw [show 0 + (2 * d + 4) = 2 * d + 4 from by ring,
      show r + (2 * d + 4) = 2 * d + r + 4 from by ring] at h
  exact h

-- Main transition: one full cycle
-- (0, 0, 0, d, d+r+1) ⊢⁺ (0, 0, 0, 2d+2, 2d+r+4)
theorem main_trans (d r : ℕ) :
    ⟨0, 0, 0, d, d+r+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*d+2, 2*d+r+4⟩ := by
  -- Phase 1: (0,0,0,d,d+r+1) ->* (0,0,2d,0,r+1)
  apply stepStar_stepPlus_stepPlus
  · have h := phase1 d 0 0 (r+1)
    rw [show 0 + d = d from by ring,
        show (r + 1) + d = d + r + 1 from by ring,
        show 0 + 2 * d = 2 * d from by ring] at h
    exact h
  -- Phase 2 (R5 step): (0,0,2d,0,r+1) -> (0,2,2d,0,r)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2 * d, 0, r + 1⟩ = some ⟨0, 2, 2 * d, 0, r⟩; simp [fm]
  -- Phase 3 (R2,R2): (0,2,2d,0,r) ->* (4,0,2d,2,r)
  apply stepStar_trans
  · show ⟨0, 2, 2 * d, 0, r⟩ [fm]⊢* ⟨4, 0, 2 * d, 2, r⟩
    step fm; step fm; finish
  -- Phases 4+5
  exact phase45 d r

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, r⟩ ↦ ⟨0, 0, 0, d, d + r + 1⟩) ⟨0, 0⟩
  intro ⟨d, r⟩
  refine ⟨⟨2*d+2, r+1⟩, ?_⟩
  show ⟨0, 0, 0, d, d + r + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 2, 2 * d + 2 + (r + 1) + 1⟩
  rw [show 2 * d + 2 + (r + 1) + 1 = 2 * d + r + 4 from by ring]
  exact main_trans d r

end Sz22_2003_unofficial_414
