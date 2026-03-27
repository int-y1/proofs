import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #180: [1/6, 1225/33, 3/5, 4/7, 363/2]

Vector representation:
```
-1 -1  0  0  0
 0 -1  2  2 -1
 0  1 -1  0  0
 2  0  0 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_180

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d+2, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- Phase 1: R5,R1 alternation - transfer a to b,e
-- (a+2, 1, 0, 0, e) ->* (a, 1, 0, 0, e+4) when a >= 0 (one R1 + two R5 steps... no)
-- Actually: (a+2, b, 0, 0, e) with b=0: R5 fires -> (a+1, 1, 0, 0, e+2), R1 fires -> (a, 0, 0, 0, e+2)
-- So pair (R5, R1): a -= 2, e += 2, net. Let's do it as a chain.

-- R5,R1 pair: (a+2, 0, 0, 0, e) ->* (a, 0, 0, 0, e+4) via 2 steps... no.
-- (a+2, 0, 0, 0, e): R5 -> (a+1, 1, 0, 0, e+2), R1 -> (a, 0, 0, 0, e+2). That's +2 to e not +4.

-- Chain of R5,R1 pairs
theorem r5r1_chain : ∀ j a e,
    ⟨a + 2*j, 0, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + 2*j⟩ := by
  intro j; induction' j with j ih <;> intro a e
  · exists 0
  rw [show a + 2 * (j + 1) = (a + 2 * j) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  rw [show (e + 2) + 2 * j = e + 2 * (j + 1) from by ring]
  finish

-- Final R5 step when a is odd: (1, 0, 0, 0, e) -> (0, 1, 0, 0, e+2)
-- Phase 1 total: (2k+1, 0, 0, 0, 0) ->* (0, 1, 0, 0, 2k+2)
-- We get there via r5r1_chain with j=k, a=1, then one R5 step... wait
-- (2k+1, 0, 0, 0, 0) = (1 + 2k, 0, 0, 0, 0), apply r5r1_chain k:
-- -> (1, 0, 0, 0, 2k), then R5: (0, 1, 0, 0, 2k+2)

-- Phase 2: R2,R3 loop consuming e
-- Starting from (0, 1, 0, 0, 2k+2):
-- R2: (0, 0, 2, 2, 2k+1)
-- Then (R3, R2) loop j times: (0, 0, 2+j, 2+2j, 2k+1-j)
-- When j = 2k+1: (0, 0, 2k+3, 4k+4, 0)

-- One (R3, R2) step
theorem r3r2_one : ∀ c d e,
    ⟨0, 0, c+1, d, e+1⟩ [fm]⊢* ⟨0, 0, c+2, d+2, e⟩ := by
  intro c d e
  step fm; step fm; finish

-- Chain of (R3, R2) steps
theorem r3r2_chain : ∀ j c d e,
    ⟨0, 0, c+1, d, e+j⟩ [fm]⊢* ⟨0, 0, c+1+j, d+2*j, e⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  rw [show e + (j + 1) = (e + j) + 1 from by ring]
  apply stepStar_trans (r3r2_one _ _ _)
  rw [show c + 2 = (c + 1) + 1 from by ring,
      show d + 2 = d + 2 from rfl]
  apply stepStar_trans (ih (c + 1) (d + 2) e)
  rw [show (c + 1) + 1 + j = c + 1 + (j + 1) from by ring,
      show (d + 2) + 2 * j = d + 2 * (j + 1) from by ring]
  finish

-- Phase 3: R3 chain - transfer c to b
theorem r3_chain : ∀ j b c d,
    ⟨0, b, c+j, d, 0⟩ [fm]⊢* ⟨0, b+j, c, d, 0⟩ := by
  intro j; induction' j with j ih <;> intro b c d
  · exists 0
  rw [show c + (j + 1) = (c + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  rw [show (b + 1) + j = b + (j + 1) from by ring]
  finish

-- Phase 4a: (R4, R1, R1) loop - consumes b by 2 and d by 1
theorem r4r1r1_one : ∀ b d,
    ⟨0, b+2, 0, d+1, 0⟩ [fm]⊢* ⟨0, b, 0, d, 0⟩ := by
  intro b d
  step fm; step fm; step fm; finish

theorem r4r1r1_chain : ∀ j b d,
    ⟨0, b+2*j, 0, d+j, 0⟩ [fm]⊢* ⟨0, b, 0, d, 0⟩ := by
  intro j; induction' j with j ih <;> intro b d
  · exists 0
  rw [show b + 2 * (j + 1) = (b + 2 * j) + 2 from by ring,
      show d + (j + 1) = (d + j) + 1 from by ring]
  apply stepStar_trans (r4r1r1_one _ _)
  exact ih _ _

-- Phase 4b: tail when b=1: (0, 1, 0, d+1, 0) -> (1, 0, 0, d, 0)
theorem tail_b1 : ∀ d,
    ⟨0, 1, 0, d+1, 0⟩ [fm]⊢* ⟨1, 0, 0, d, 0⟩ := by
  intro d
  step fm; step fm; finish

-- Phase 4c: R4 chain - transfer d to a
theorem r4_chain : ∀ j a d,
    ⟨a, 0, 0, d+j, 0⟩ [fm]⊢* ⟨a+2*j, 0, 0, d, 0⟩ := by
  intro j; induction' j with j ih <;> intro a d
  · exists 0
  rw [show d + (j + 1) = (d + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  rw [show (a + 2) + 2 * j = a + 2 * (j + 1) from by ring]
  finish

-- Main transition: (2k+1, 0, 0, 0, 0) ->+ (6k+5, 0, 0, 0, 0)
theorem main_trans (k : ℕ) :
    ⟨2*k+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨2*(3*k+2)+1, 0, 0, 0, 0⟩ := by
  -- Phase 1: R5,R1 chain then final R5
  -- (2k+1, 0, 0, 0, 0) ->* (1, 0, 0, 0, 2k) -> (0, 1, 0, 0, 2k+2)
  apply stepStar_stepPlus_stepPlus
  · have h := r5r1_chain k 1 0
    rw [show 1 + 2 * k = 2 * k + 1 from by ring,
        show 0 + 2 * k = 2 * k from by ring] at h
    exact h
  -- Now at (1, 0, 0, 0, 2k). R5 fires.
  apply step_stepStar_stepPlus
  · show fm ⟨1, 0, 0, 0, 2 * k⟩ = some ⟨0, 1, 0, 0, 2 * k + 2⟩; rfl
  -- Phase 2: R2 step then R3,R2 chain
  -- (0, 1, 0, 0, 2k+2) -> (0, 0, 2, 2, 2k+1) ->* (0, 0, 2k+3, 4k+4, 0)
  apply stepStar_trans
  · show ⟨0, 1, 0, 0, 2 * k + 2⟩ [fm]⊢* ⟨0, 0, 2, 2, 2 * k + 1⟩
    step fm; finish
  apply stepStar_trans
  · have h := r3r2_chain (2*k+1) 1 2 0
    rw [show 0 + (2 * k + 1) = 2 * k + 1 from by ring,
        show 1 + 1 + (2 * k + 1) = 2 * k + 3 from by ring,
        show 2 + 2 * (2 * k + 1) = 4 * k + 4 from by ring] at h
    exact h
  -- Phase 3: R3 chain
  -- (0, 0, 2k+3, 4k+4, 0) ->* (0, 2k+3, 0, 4k+4, 0)
  apply stepStar_trans
  · have h := r3_chain (2*k+3) 0 0 (4*k+4)
    rw [show 0 + (2 * k + 3) = 2 * k + 3 from by ring] at h
    exact h
  -- Phase 4a: (R4, R1, R1) chain
  -- b = 2k+3, d = 4k+4. After (k+1) iterations of (R4,R1,R1):
  -- b = 2k+3 - 2(k+1) = 1, d = 4k+4 - (k+1) = 3k+3
  -- (0, 2k+3, 0, 4k+4, 0) ->* (0, 1, 0, 3k+3, 0)
  apply stepStar_trans
  · have h := r4r1r1_chain (k+1) 1 (3*k+3)
    rw [show 1 + 2 * (k + 1) = 2 * k + 3 from by ring,
        show (3 * k + 3) + (k + 1) = 4 * k + 4 from by ring] at h
    exact h
  -- Phase 4b: tail
  -- (0, 1, 0, 3k+3, 0) ->* (1, 0, 0, 3k+2, 0)
  apply stepStar_trans
  · have h := tail_b1 (3*k+2)
    rw [show (3 * k + 2) + 1 = 3 * k + 3 from by ring] at h
    exact h
  -- Phase 4c: R4 chain
  -- (1, 0, 0, 3k+2, 0) ->* (6k+5, 0, 0, 0, 0)
  have h := r4_chain (3*k+2) 1 0
  rw [show 0 + (3 * k + 2) = 3 * k + 2 from by ring,
      show 1 + 2 * (3 * k + 2) = 2 * (3 * k + 2) + 1 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨2*k+1, 0, 0, 0, 0⟩) 0
  intro k
  exact ⟨3*k+2, main_trans k⟩

end Sz22_2003_unofficial_180
