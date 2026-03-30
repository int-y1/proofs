import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1121: [5/6, 41503/2, 2/35, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  3  2
 1  0 -1 -1  0
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1121

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+2⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Phase 1: Move d to b (R4 repeated). Needs a=0, c=0.
theorem d_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- Phase 2: R2+R3 chain. From (1, 0, c, d, e), repeatedly apply R2 then R3.
-- Each round: (1,0,c,d,e) -> R2 -> (0,0,c,d+3,e+2) -> R3 -> (1,0,c-1,d+2,e+2).
-- After c rounds: (1,0,0,d+2c,e+2c) -> R2 -> (0,0,0,d+2c+3,e+2c+2).
theorem r2r3_chain : ∀ c, ∀ d e, ⟨1, 0, c, d, e⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2 * c + 3, e + 2 * c + 2⟩ := by
  intro c; induction' c with c ih <;> intro d e
  · step fm; finish
  · rw [show d + 2 * (c + 1) + 3 = (d + 2) + 2 * c + 3 from by ring,
        show e + 2 * (c + 1) + 2 = (e + 2) + 2 * c + 2 from by ring]
    step fm  -- R2: (0, 0, c+1, d+3, e+2)
    step fm  -- R3: (1, 0, c, d+2, e+2)
    exact stepPlus_stepStar (ih (d + 2) (e + 2))

-- Phase 3: Mixing phase. From (0, 2k+1, c, 0, e+k+1), interleave R5,R1,R3,R1.
-- Each round: b -= 2, e -= 1, c += 1. After k rounds + final 3 steps:
-- Result: (1, 0, c+k, 0, e).
theorem mixing : ∀ k, ∀ c e, ⟨0, 2 * k + 1, c, 0, e + k + 1⟩ [fm]⊢* ⟨1, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · -- k=0: (0, 1, c, 0, e+1). R5, R1, R3.
    step fm  -- R5: (1, 1, c, 1, e)
    step fm  -- R1: (0, 0, c+1, 1, e)
    step fm  -- R3: (1, 0, c, 0, e)
    finish
  · -- k+1: (0, 2*(k+1)+1, c, 0, e+(k+1)+1) = (0, 2*k+3, c, 0, e+k+2)
    rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm  -- R5: (1, 2*k+3, c, 1, e+k+1)
    rw [show (2 * k + 2) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm  -- R1: (0, 2*k+2, c+1, 1, e+k+1)
    rw [show (2 * k + 1) + 1 = (2 * k + 1) + 1 from rfl]
    step fm  -- R3: (1, 2*k+1+1, c, 0, e+k+1)
    rw [show (2 * k + 1) + 1 = (2 * k) + 1 + 1 from by ring]
    step fm  -- R1: (0, 2*k+1, c+1, 0, e+k+1)
    apply stepStar_trans (ih (c := c + 1) (e := e))
    ring_nf; finish

-- Main transition: (0, 0, 0, 2*k+3, e) ->+ (0, 0, 0, 2*k+5, e+k+2)
-- when e >= k+2.
-- Steps: d_to_b -> mixing -> r2r3_chain.
-- d_to_b: (0, 0, 0, 2*k+3, e) ->* (0, 2*k+3, 0, 0, e)
-- mixing with e = e - k - 2 + k + 1 + 1 = e: need e >= k+2.
-- Let e = e' + k + 2. Then:
-- mixing: (0, 2*k+3, 0, 0, e'+k+2) = (0, 2*(k+1)+1, 0, 0, e'+(k+1)+1)
--   ->* (1, 0, k+1, 0, e')
-- r2r3_chain: (1, 0, k+1, 0, e') ->+ (0, 0, 0, 2*(k+1)+3, 2*(k+1)+2+e')
--   = (0, 0, 0, 2*k+5, e'+2*k+4)
-- So from (0, 0, 0, 2*k+3, e'+k+2) we reach (0, 0, 0, 2*k+5, e'+2*k+4).
-- e' + 2*k + 4 = (e'+k+2) + (k+2). So e' = e - k - 2, new_e = e + k + 2.

theorem main_trans : ∀ k e, ⟨0, 0, 0, 2 * k + 3, e + k + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * k + 5, e + 2 * k + 4⟩ := by
  intro k e
  -- d_to_b
  apply stepStar_stepPlus_stepPlus
  · rw [show (2 * k + 3 : ℕ) = 0 + (2 * k + 3) from by ring]
    exact d_to_b (2 * k + 3) 0 0 (e + k + 2)
  -- mixing
  apply stepStar_stepPlus_stepPlus
  · rw [show (0 : ℕ) + (2 * k + 3) = 2 * (k + 1) + 1 from by ring,
        show e + k + 2 = e + (k + 1) + 1 from by ring]
    exact mixing (k + 1) 0 e
  -- r2r3_chain
  rw [show (0 : ℕ) + (k + 1) = k + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (r2r3_chain (k + 1) 0 e)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k e, q = ⟨0, 0, 0, 2 * k + 3, e + k + 2⟩)
  · intro c ⟨k, e, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, 2 * k + 5, e + 2 * k + 4⟩,
      ⟨k + 1, e + k + 1, by ring_nf⟩,
      main_trans k e⟩
  · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_1121
