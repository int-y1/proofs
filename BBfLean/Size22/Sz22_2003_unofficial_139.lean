import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #139: [1/45, 2/35, 715/2, 147/11, 5/39]

Vector representation:
```
 0 -2 -1  0  0  0
 1  0 -1 -1  0  0
-1  0  1  0  1  1
 0  1  0  2 -1  0
 0 -1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_139

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+2, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- Phase A: initial setup from canonical state
-- (0,0,1,0,e+1,f) -> (0,0,0,2,e+1,f+2) in 7 steps
theorem phase_a : ⟨0, 0, 1, 0, e+1, f⟩ [fm]⊢* ⟨0, 0, 0, 2, e+1, f+2⟩ := by
  execute fm 7

-- R4 chain: (0,b,0,d,e,f) ->* (0,b+e,0,d+2*e,0,f) by induction on e
theorem r4_chain : ∀ e, ∀ b d f, ⟨0, b, 0, d, e, f⟩ [fm]⊢* ⟨0, b+e, 0, d+2*e, 0, f⟩ := by
  intro e; induction' e with e ih <;> intro b d f
  · exists 0
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Drain step: R5 + R1, removing 3 from b and 1 from f
-- (0,k+3,0,D,0,F+1) -> (0,k,0,D,0,F) in 2 steps
theorem drain_step : ⟨0, k+3, 0, D, 0, F+1⟩ [fm]⊢* ⟨0, k, 0, D, 0, F⟩ := by
  step fm; step fm; finish

-- Drain base: R5 + R2
-- (0,1,0,D+1,0,F+1) -> (1,0,0,D,0,F) in 2 steps
theorem drain_base : ⟨0, 1, 0, D+1, 0, F+1⟩ [fm]⊢* ⟨1, 0, 0, D, 0, F⟩ := by
  step fm; step fm; finish

-- Drain iterated: (0,3*m+1,0,D+1,0,F+m+1) ->* (1,0,0,D,0,F) by induction on m
theorem drain_iter : ∀ m, ∀ D F, ⟨0, 3*m+1, 0, D+1, 0, F+m+1⟩ [fm]⊢* ⟨1, 0, 0, D, 0, F⟩ := by
  intro m; induction' m with m ih <;> intro D F
  · exact drain_base
  rw [show 3 * (m + 1) + 1 = (3 * m + 1) + 3 from by ring,
      show F + (m + 1) + 1 = (F + m + 1) + 1 from by ring]
  apply stepStar_trans drain_step
  exact ih _ _

-- R2+R3 step: (0,0,1,d+1,e,f) -> (0,0,1,d,e+1,f+1) in 2 steps
theorem r2r3_step : ⟨0, 0, 1, d+1, e, f⟩ [fm]⊢* ⟨0, 0, 1, d, e+1, f+1⟩ := by
  step fm; step fm; finish

-- R2+R3 chain: (0,0,1,d,e,f) ->* (0,0,1,0,e+d,f+d) by induction on d
theorem r2r3_chain : ∀ d, ∀ e f, ⟨0, 0, 1, d, e, f⟩ [fm]⊢* ⟨0, 0, 1, 0, e+d, f+d⟩ := by
  intro d; induction' d with d ih <;> intro e f
  · exists 0
  rw [show d + 1 = (d) + 1 from rfl]
  apply stepStar_trans r2r3_step
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase D: (1,0,0,d,0,f) ->+ (0,0,1,0,d+1,f+d+1) via R3 then R2+R3 chain
theorem phase_d : ⟨1, 0, 0, d, 0, f⟩ [fm]⊢⁺ ⟨0, 0, 1, 0, d+1, f+d+1⟩ := by
  step fm
  apply stepStar_trans (r2r3_chain d _ _)
  ring_nf; finish

-- Main transition: (0,0,1,0,3*m+1,5*m+1) ->+ (0,0,1,0,6*m+4,10*m+6)
theorem main_trans (m : ℕ) :
    ⟨0, 0, 1, 0, 3*m+1, 5*m+1⟩ [fm]⊢⁺ ⟨0, 0, 1, 0, 6*m+4, 10*m+6⟩ := by
  -- Phase A: (0,0,1,0,3m+1,5m+1) ->* (0,0,0,2,3m+1,5m+3)
  rw [show 3*m+1 = (3*m) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (phase_a (e := 3*m) (f := 5*m+1))
  -- Now at (0,0,0,2,3m+1,5m+3). Note: 3m+1 = 3*m + 1 from phase_a output but e+1 form.
  -- Actually phase_a gives (0,0,0,2,3*m+1,5*m+1+2) = (0,0,0,2,3*m+1,5*m+3)
  -- Phase B: R4 chain (0,0,0,2,3m+1,5m+3) ->* (0,3m+1,0,2+2*(3m+1),0,5m+3)
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (3*m+1) 0 2 (5*m+3)
    simp only [Nat.zero_add] at h
    exact h
  -- Now at (0,3m+1,0,2+2*(3m+1),0,5m+3) = (0,3m+1,0,6m+4,0,5m+3)
  -- Phase C: drain (0,3m+1,0,6m+4,0,5m+3) ->* (1,0,0,6m+3,0,4m+2)
  -- Rewrite to match drain_iter: (0,3*m+1,0,(6m+3)+1,0,(4m+2)+m+1)
  -- Check: (4m+2)+m+1 = 5m+3. Yes!
  -- 2+2*(3*m+1) = 6m+4 = (6m+3)+1. Yes!
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 + 2 * (3 * m + 1) = (6*m+3)+1 from by ring,
        show 5*m+3 = (4*m+2)+m+1 from by ring]
    exact drain_iter m (6*m+3) (4*m+2)
  -- Now at (1,0,0,6m+3,0,4m+2)
  -- Phase D: (1,0,0,6m+3,0,4m+2) ->+ (0,0,1,0,6m+4,10m+6)
  have h := @phase_d (6*m+3) (4*m+2)
  rw [show 6*m+3+1 = 6*m+4 from by ring,
      show 4*m+2+(6*m+3)+1 = 10*m+6 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨0, 0, 1, 0, 3*m+1, 5*m+1⟩) 0
  intro m
  refine ⟨2*m+1, ?_⟩
  rw [show 3*(2*m+1)+1 = 6*m+4 from by ring,
      show 5*(2*m+1)+1 = 10*m+6 from by ring]
  exact main_trans m

end Sz22_2003_unofficial_139
