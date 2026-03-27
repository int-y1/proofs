import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #156: [1/45, 35/2, 26/55, 363/7, 5/169]

Vector representation:
```
 0 -2 -1  0  0  0
-1  0  1  1  0  0
 1  0 -1  0 -1  1
 0  1  0 -1  2  0
 0  0  1  0  0 -2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_156

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+2, f⟩
  | ⟨a, b, c, d, e, f+2⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- Phase 1: R3,R2 alternation. Each pair transfers 1 from e to d and f.
theorem r3r2_loop : ∀ j d e f,
    ⟨0, 1, 1, d, e+j, f⟩ [fm]⊢* ⟨0, 1, 1, d+j, e, f+j⟩ := by
  intro j; induction' j with j ih <;> intro d e f
  · exists 0
  rw [show e + (j + 1) = (e + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 chain: transfers d to b and e.
theorem r4_chain : ∀ j b d e g,
    ⟨0, b, 0, d+j, e, g⟩ [fm]⊢* ⟨0, b+j, 0, d, e+2*j, g⟩ := by
  intro j; induction' j with j ih <;> intro b d e g
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- Phase 3: R5,R1 drain.
theorem r5r1_drain : ∀ j e,
    ⟨0, 2*j+1, 0, 0, e, 2*j+2⟩ [fm]⊢* ⟨0, 1, 1, 0, e, 0⟩ := by
  intro j; induction' j with j ih <;> intro e
  · step fm; finish
  rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 from by ring,
      show 2 * (j + 1) + 2 = (2 * j + 2) + 2 from by ring]
  step fm; step fm
  exact ih _

-- Main transition: (0,1,1,0,2*(n+1),0) ->+ (0,1,1,0,4*(n+1),0)
theorem main_trans (n : ℕ) :
    ⟨0, 1, 1, 0, 2*(n+1), 0⟩ [fm]⊢⁺ ⟨0, 1, 1, 0, 4*(n+1), 0⟩ := by
  -- Phase 1: R3,R2 loop for 2*(n+1) iterations
  -- (0,1,1,0,2*(n+1),0) ->* (0,1,1,2*(n+1),0,2*(n+1))
  apply stepStar_stepPlus_stepPlus
  · have h := r3r2_loop (2*(n+1)) 0 0 0
    simp only [(by ring : 0 + (2*(n+1)) = 2*(n+1))] at h
    exact h
  -- Phase 2: (0,1,1,2*(n+1),0,2*(n+1))
  -- R4: (0,2,1,2*n+1,2,2*(n+1))
  -- R1: (0,0,0,2*n+1,2,2*(n+1))
  -- R4 chain (2*n+1 steps): (0,2*n+1,0,0,4*(n+1),2*(n+1))
  apply step_stepStar_stepPlus
  · show fm ⟨0, 1, 1, 2 * (n + 1), 0, 2 * (n + 1)⟩ = _; rfl
  step fm
  apply stepStar_trans
  · have h := r4_chain (2*n+1) 0 0 2 (2*(n+1))
    simp only [(by ring : 0 + (2*n+1) = 2*n+1),
               (by ring : 2 + 2*(2*n+1) = 4*(n+1))] at h
    exact h
  -- Phase 3: R5,R1 drain
  -- (0,2*n+1,0,0,4*(n+1),2*(n+1)) ->* (0,1,1,0,4*(n+1),0)
  have h := r5r1_drain n (4*(n+1))
  rw [show 2*n+2 = 2*(n+1) from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 1, 0, 2, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 1, 1, 0, 2*(n+1), 0⟩) 0
  intro n
  exact ⟨2*n+1, by rw [show 2*(2*n+1+1) = 4*(n+1) from by ring]; exact main_trans n⟩

end Sz22_2003_unofficial_156
