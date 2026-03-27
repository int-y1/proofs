import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #9: [1/105, 4/3, 15/22, 49/2, 363/7]

Vector representation:
```
 0 -1 -1 -1  0
 2 -1  0  0  0
-1  1  1  0 -1
-1  0  0  2  0
 0  1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_9

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R2/R1 chain: when b=0, d=0
-- Each round: R2 gives (a, 1, c+1, 0, e-1), then R1 (since d=0) gives (a+2, 0, c+1, 0, e-1)
-- (a+1, 0, c, 0, e+k) ->* (a+k+1, 0, c+k, 0, e)
theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a+1, 0, c, 0, e+k⟩ [fm]⊢* ⟨a+k+1, 0, c+k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R2: (a, 1, c+1, 0, e+k)
  step fm  -- R1 (d=0): (a+2, 0, c+1, 0, e+k)
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 drain: (a+k, 0, c, d, 0) ->* (a, 0, c, d+2*k, 0)
theorem r3_drain : ∀ k, ∀ a c d,
    ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm  -- R3: (a+k, 0, c, d+2, 0)
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4/R0 chain: (0, 0, c+k, d+2*k+1, e) ->* (0, 0, c, d+1, e+2*k)
-- Each round: R4 on d+2*k+1 gives (0, 1, c+k, d+2*k, e+2)
--   then R0 on (0, 1, c+k, d+2*k, e+2) with c+k >= 1 and d+2*k >= 1
--   But we need d+2*k >= 1. Since k decreases by 1 each time and d+1 >= 1 at base, this works.
-- Actually let me reformulate: (0, 0, c+k, d+1+2*k, e) ->* (0, 0, c, d+1, e+2*k)
theorem r4r0_chain : ∀ k, ∀ c d e,
    ⟨0, 0, c+k, d+1+2*k, e⟩ [fm]⊢* ⟨0, 0, c, d+1, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + 1 + 2 * (k + 1) = (d + 1 + 2 * k) + 1 + 1 from by ring]
  step fm  -- R4: (0, 1, c+k+1, d+1+2*k+1, e+2)
  step fm  -- R0: (0, 0, c+k, d+1+2*k, e+2)
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Full star transition: (1, 0, 0, 0, e+1) ->* (0, 0, 0, 2, 2*e+2)
theorem full_star (e : ℕ) :
    ⟨1, 0, 0, 0, e+1⟩ [fm]⊢* ⟨0, 0, 0, 2, 2*e+2⟩ := by
  -- R2: (0, 1, 1, 0, e)
  step fm
  -- R1 (d=0): (2, 0, 1, 0, e)
  step fm
  -- Phase 1: R2/R1 chain e times: (2, 0, 1, 0, e) ->* (e+2, 0, e+1, 0, 0)
  rw [show (2 : ℕ) = 1 + 1 from by ring, show e = 0 + e from by ring]
  apply stepStar_trans (r2r1_chain e 1 1 0)
  -- Now at (1+e+1, 0, 1+e, 0, 0)
  -- Phase 2: R3 drain: ->* (0, 0, 1+e, 2*(1+e+1), 0)
  rw [show 1 + e + 1 = 0 + (e + 2) from by ring]
  apply stepStar_trans (r3_drain (e+2) 0 (1+e) 0)
  -- Now at (0, 0, 1+e, 0+2*(e+2), 0)
  -- Phase 3: R4/R0 chain (e+1) times
  rw [show 1 + e = 0 + (e + 1) from by ring,
      show 0 + 2 * (e + 2) = 1 + 1 + 2 * (e + 1) from by ring]
  apply stepStar_trans (r4r0_chain (e+1) 0 1 0)
  ring_nf; finish

-- End steps: (0, 0, 0, 2, 2*e+2) ⊢⁺ (1, 0, 0, 0, 2*e+3)
theorem end_steps (e : ℕ) :
    ⟨0, 0, 0, 2, 2*e+2⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2*e+3⟩ := by
  -- R4: (0, 1, 0, 1, 2*e+4)
  step fm
  -- R1 (c=0, d≠0 but R1 requires b+1): (2, 0, 0, 1, 2*e+4)
  step fm
  -- R2: (1, 1, 1, 1, 2*e+3)
  rw [show 2 * e + 2 + 2 = (2 * e + 3) + 1 from by ring]
  step fm
  -- R0: (1, 0, 0, 0, 2*e+3)
  step fm
  finish

-- Main transition
theorem main_trans (e : ℕ) :
    ⟨1, 0, 0, 0, e+1⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2*e+3⟩ :=
  stepStar_stepPlus_stepPlus (full_star e) (end_steps e)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, 0, n+1⟩) 0
  intro n
  exact ⟨2*n+2, main_trans n⟩

end Sz22_2003_unofficial_9
