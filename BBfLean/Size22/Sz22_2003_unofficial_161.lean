import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #161: [1/45, 4/3, 15/14, 11/2, 441/11]

Vector representation:
```
 0 -2 -1  0  0
 2 -1  0  0  0
-1  1  1 -1  0
-1  0  0  0  1
 0  2  0  2 -1
```

This Fractran program doesn't halt. The canonical state is `(0, 0, c, 0, c+f+1)`
with transition `(c, f) -> (2*c+2, f+3)`.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_161

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+2, e⟩
  | _ => none

-- Phase 1: R5+R1 drain loop, j iterations
-- (0, 0, c+j, 2*d, e+j) ->* (0, 0, c, 2*(d+j), e)
theorem drain_iter : ∀ j, ∀ c d e,
    ⟨0, 0, c+j, 2*d, e+j⟩ [fm]⊢* ⟨0, 0, c, 2*(d+j), e⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · simp; exists 0
  rw [show c+(j+1) = (c+1)+j from by ring,
      show e+(j+1) = (e+1)+j from by ring]
  apply stepStar_trans (ih (c+1) d (e+1))
  step fm; step fm
  rw [show d+(j+1) = (d+j)+1 from by ring]
  ring_nf; finish

-- Phase 3: R3+R2 chain, j iterations
-- (a+1, 0, c, d+j, e) ->* (a+1+j, 0, c+j, d, e)
theorem r3r2_chain : ∀ j, ∀ a c d e,
    ⟨a+1, 0, c, d+j, e⟩ [fm]⊢* ⟨a+1+j, 0, c+j, d, e⟩ := by
  intro j; induction' j with j ih <;> intro a c d e
  · exists 0
  rw [show d+(j+1) = (d+j)+1 from by ring]
  step fm; step fm
  rw [show a+2 = (a+1)+1 from by ring]
  apply stepStar_trans (ih (a+1) (c+1) d e)
  ring_nf; finish

-- Phase 4: R4 dump, j iterations
-- (j, 0, c, 0, e) ->* (0, 0, c, 0, e+j)
theorem r4_dump : ∀ j, ∀ c e,
    ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e+j⟩ := by
  intro j; induction' j with j ih <;> intro c e
  · exists 0
  step fm
  apply stepStar_trans (ih c (e+1))
  ring_nf; finish

-- Main transition
theorem main_trans (c f : ℕ) :
    ⟨0, 0, c, 0, c+f+1⟩ [fm]⊢⁺ ⟨0, 0, 2*c+2, 0, (2*c+2)+(f+3)+1⟩ := by
  -- Phase 1: drain c iterations (stepStar)
  apply stepStar_stepPlus_stepPlus
  · have h := drain_iter c 0 0 (f+1)
    simp only [Nat.mul_zero,
               show (f+1)+c = c+f+1 from by ring,
               show 0+c = c from by ring] at h
    exact h
  -- Now at (0, 0, 0, 2*c, f+1). Phase 2: R5 step (starts stepPlus)
  step fm
  -- Now at (0, 2, 0, 2*c+2, f). R2 step.
  step fm
  -- Now at (2, 1, 0, 2*c+2, f). R2 step.
  step fm
  -- Now at (4, 0, 0, 2*c+2, f).
  -- Phase 3: R3+R2 chain, 2*c+2 iterations
  apply stepStar_trans
  · have h := r3r2_chain (2*c+2) 3 0 0 f
    simp only [show 3+1 = 4 from by ring, Nat.zero_add,
               show 3+1+(2*c+2) = 2*c+6 from by ring] at h
    exact h
  -- Now at (2*c+6, 0, 2*c+2, 0, f). Phase 4: R4 dump.
  have h := r4_dump (2*c+6) (2*c+2) f
  rw [show f+(2*c+6) = (2*c+2)+(f+3)+1 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 6⟩) (by execute fm 14)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, f⟩ ↦ ⟨0, 0, c, 0, c+f+1⟩) ⟨2, 3⟩
  intro ⟨c, f⟩
  exact ⟨⟨2*c+2, f+3⟩, main_trans c f⟩

end Sz22_2003_unofficial_161
