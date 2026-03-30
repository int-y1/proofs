import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #781: [35/6, 55/2, 8/77, 3/5, 49/3]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  1
 3  0  0 -1 -1
 0  1 -1  0  0
 0 -1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_781

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | _ => none

-- R4 chain: move c to b. (0, b, c+k, 0, e) →* (0, b+k, c, 0, e)
theorem r4_chain : ∀ k, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R2/R3 drain: (0, 0, c, d, e+1) →* (0, 0, c + 3*d, 0, e + 2*d + 1)
-- Each round: R3 then R2x3, d times total.
theorem r2r3_drain : ∀ d, ⟨0, 0, c, d, e + 1⟩ [fm]⊢* ⟨0, 0, c + 3 * d, 0, e + 2 * d + 1⟩ := by
  intro d; induction' d with d ih generalizing c e
  · exists 0
  · step fm -- R3: (3, 0, c, d, e)
    step fm; step fm; step fm -- R2 x 3: (0, 0, c+3, d, e+3)
    rw [show e + 3 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih (c := c + 3) (e := e + 2))
    ring_nf; finish

-- R1x3+R3 chain: (3, b+3, c, d, e+1) →* (3, b, c+3, d+2, e)
-- One round: R1 x 3 then R3.
-- After k rounds: (3, 3*k+b, c, d, e+k) →* (3, b, c+3*k, d+2*k, e)
theorem r1r3_chain : ∀ k, ⟨3, 3 * k + b, c, d, e + k⟩ [fm]⊢* ⟨3, b, c + 3 * k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · simp; exists 0
  · rw [show 3 * (k + 1) + b = (3 * k + (b + 3)) from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b := b + 3) (e := e + 1))
    -- Now: (3, b+3, c+3*k, d+2*k, e+1)
    step fm; step fm; step fm -- R1 x 3: (0, b, c+3*k+3, d+2*k+3, e+1)
    step fm -- R3: (3, b, c+3*k+3, d+2*k+2, e)
    ring_nf; finish

-- Full cycle: (0, 3*(m+1), 0, 0, e) →⁺ (0, 3*(3*m+4), 0, 0, e+3*m+6) when e >= m+1
-- Decomposition:
-- 1. R5: (0, 3*(m+1), 0, 0, e) -> (0, 3*m+2, 0, 2, e)
-- 2. R3: (0, 3*m+2, 0, 2, e) -> (3, 3*m+2, 0, 1, e-1) [needs e >= 1]
-- 3. R1x3+R3 chain m times: (3, 3*m+2, 0, 1, e-1) ->* (3, 2, 3*m, 2*m+1, e-1-m)
-- 4. R1 x 2: (3, 2, 3*m, 2*m+1, e-m-1) -> (1, 0, 3*m+2, 2*m+3, e-m-1)
-- 5. R2: (1, 0, 3*m+2, 2*m+3, e-m-1) -> (0, 0, 3*m+3, 2*m+3, e-m)
-- 6. R2/R3 drain: (0, 0, 3*m+3, 2*m+3, e-m) ->* (0, 0, 9*m+12, 0, e+3*m+6)
-- 7. R4 chain: (0, 0, 9*m+12, 0, e+3*m+6) ->* (0, 9*m+12, 0, 0, e+3*m+6)
theorem main_cycle (m e : ℕ) (he : e ≥ m + 1) :
    ⟨0, 3 * (m + 1), 0, 0, e⟩ [fm]⊢⁺ ⟨0, 3 * (3 * m + 4), 0, 0, e + 3 * m + 6⟩ := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + (m + 1) := ⟨e - (m + 1), by omega⟩
  -- State: (0, 3*(m+1), 0, 0, e'+(m+1))
  -- Step 1: R5
  rw [show 3 * (m + 1) = (3 * m + 2) + 1 from by ring]
  step fm -- R5: (0, 3*m+2, 0, 2, e'+m+1)
  -- Step 2: R3
  rw [show e' + (m + 1) = e' + m + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm -- R3: (3, 3*m+2, 0, 1, e'+m)
  -- Step 3: R1x3+R3 chain, m rounds
  rw [show 3 * m + 2 = 3 * m + 2 from rfl,
      show e' + m = e' + m from rfl]
  apply stepStar_trans (r1r3_chain m (b := 2) (c := 0) (d := 1) (e := e'))
  -- State: (3, 2, 3*m, 2*m+1, e')
  -- Step 4: R1 x 2
  step fm; step fm -- R1 x 2: (1, 0, 3*m+2, 2*m+3, e')
  -- Step 5: R2
  step fm -- R2: (0, 0, 3*m+3, 2*m+3, e'+1)
  -- Normalize arithmetic before R2/R3 drain
  rw [show 0 + 3 * m + 1 + 1 + 1 = 3 * m + 3 from by ring,
      show 1 + 2 * m + 1 + 1 = 2 * m + 3 from by ring,
      show e' + m + 1 + 3 * m + 6 = e' + 4 * m + 7 from by ring]
  -- Step 6: R2/R3 drain
  apply stepStar_trans (r2r3_drain (2 * m + 3) (c := 3 * m + 3) (e := e'))
  -- Step 7: R4 chain
  rw [show 3 * m + 3 + 3 * (2 * m + 3) = 9 * m + 12 from by ring,
      show e' + 2 * (2 * m + 3) + 1 = e' + 4 * m + 7 from by ring,
      show (9 * m + 12 : ℕ) = 0 + (9 * m + 12) from by ring]
  apply stepStar_trans (r4_chain (9 * m + 12) (b := 0) (c := 0) (e := e' + 4 * m + 7))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 6, 0, 0, 5⟩) (by execute fm 17)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m e, q = ⟨0, 3 * (m + 1), 0, 0, e⟩ ∧ e ≥ m + 1)
  · intro c ⟨m, e, hq, he⟩; subst hq
    exact ⟨⟨0, 3 * (3 * m + 4), 0, 0, e + 3 * m + 6⟩,
      ⟨3 * m + 3, e + 3 * m + 6, by ring_nf, by omega⟩, main_cycle m e he⟩
  · exact ⟨1, 5, by ring_nf, by omega⟩
