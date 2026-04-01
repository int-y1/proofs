import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1398: [7/15, 1/154, 99/7, 4/3, 175/2]

Vector representation:
```
 0 -1 -1  1  0
-1  0  0 -1 -1
 0  2  0 -1  1
 2 -1  0  0  0
-1  0  2  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1398

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

-- Phase 1: R5+R2 loop. Each round: a -= 2, c += 2, e -= 1.
-- (a + 2*k, 0, c, 0, e + k) ->* (a, 0, c + 2*k, 0, e)
-- Requires a >= 1, e + k >= 1 at each step (but we only need e >= 0 since R5 fires first).
-- Actually: R5 fires on (A+1, 0, C, 0, E) -> (A, 0, C+2, 1, E), then
-- R2 fires on (A, 0, C+2, 1, E) if A >= 1, E >= 1 -> (A-1, 0, C+2, 0, E-1).
-- So each round: a -= 2, c += 2, e -= 1. Need a >= 2 and e >= 1 at start.
theorem r5r2_loop : ∀ k, ⟨a + 2 * k, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    -- State: (a + 2*k + 2, 0, c, 0, (e+k) + 1)
    -- R5: needs a+2*k+2 >= 1. Matches R5 pattern (a'+1, 0, c, 0, (e+k)+1)
    -- where a' = a+2*k+1. Result: (a+2*k+1, 0, c+2, 1, (e+k)+1)
    step fm
    -- R2: (a+2*k+1, 0, c+2, 1, (e+k)+1) matches R2 pattern.
    -- a'+1 = a+2*k+1 so a' = a+2*k. Result: (a+2*k, 0, c+2, 0, e+k)
    step fm
    apply stepStar_trans (ih (c := c + 2))
    ring_nf; finish

-- Phase 6: R3+R1+R1 loop.
-- (0, 0, c + 2*k, d, e) ->* (0, 0, c, d + k, e + k)
-- where at each round: R3 fires (d >= 1), R1 fires twice (b >= 1, c >= 1).
-- Round: (0, 0, C+2, D+1, E) -> R3 -> (0, 2, C+2, D, E+1)
--        -> R1 -> (0, 1, C+1, D+1, E+1) -> R1 -> (0, 0, C, D+2, E+1)
-- So each round: c -= 2, d += 1, e += 1.
-- We need d >= 1 at start of each round. After first round d goes up, so we need d >= 1.
-- Start: (0, 0, 2*k, d+1, e). After k rounds: (0, 0, 0, d+1+k, e+k).
-- Actually let's be more careful. State (0, 0, C, D, E) with D >= 1.
-- R3: (0, 2, C, D-1, E+1). If C >= 1: R1: (0, 1, C-1, D, E+1). If C-1 >= 1: R1: (0, 0, C-2, D+1, E+1).
-- After round: c -= 2, d += 1, e += 1 (as long as c >= 2).
theorem r3r1r1_loop : ∀ k, ⟨0, 0, c + 2 * k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = c + 2 * k + 2 from by ring]
    -- State: (0, 0, c+2*k+2, d+1, e)
    step fm  -- R3: (0, 2, c+2*k+2, d, e+1)
    step fm  -- R1: (0, 1, c+2*k+1, d+1, e+1)
    step fm  -- R1: (0, 0, c+2*k, d+2, e+1)
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 1) (e := e + 1))
    ring_nf; finish

-- Phase 7: R3 loop. Transfer d to b (x2) and e (+1).
-- (0, b, 0, d + k, e) ->* (0, b + 2*k, 0, d, e + k)
theorem r3_loop : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R3: (0, b+2, 0, d+k, e+1)
    apply stepStar_trans (ih (b := b + 2) (e := e + 1))
    ring_nf; finish

-- Phase 8: R4 loop. Transfer b to a (x2).
-- (a, b + k, 0, 0, e) ->* (a + 2*k, b, 0, 0, e)
theorem r4_loop : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm  -- R4: (a+2, b+k, 0, 0, e)
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

-- Main transition: (2*e+2, 0, 0, 0, e) ->+ (4*e+4, 0, 0, 0, 2*e+1)
-- Phase 1: R5+R2 loop, e rounds: (2*e+2, 0, 0, 0, e) ->* (2, 0, 2*e, 0, 0)
-- Phase 2: R5: (2, 0, 2*e, 0, 0) -> (1, 0, 2*e+2, 1, 0)
-- Phase 3: R3: (1, 0, 2*e+2, 1, 0) -> (1, 2, 2*e+2, 0, 1)
-- Phase 4: R1, R1, R2: (1, 2, 2*e+2, 0, 1) -> (1, 1, 2*e+1, 1, 1)
--          -> (1, 0, 2*e, 2, 1) -> (0, 0, 2*e, 1, 0)
-- Phase 5: R3+R1+R1 loop, e rounds: (0, 0, 2*e, 1, 0) ->* (0, 0, 0, e+1, e)
-- Phase 6: R3 loop, e+1 rounds: (0, 0, 0, e+1, e) ->* (0, 2*(e+1), 0, 0, 2*e+1)
-- Phase 7: R4 loop, 2*(e+1) rounds: (0, 2*(e+1), 0, 0, 2*e+1) ->* (4*(e+1), 0, 0, 0, 2*e+1)
-- Compose the R5+R2 loop with remaining steps
theorem phase1_to_phase2 (e : ℕ) : (⟨2 * e + 2, 0, 0, 0, e⟩ : Q) [fm]⊢* ⟨2, 0, 2 * e, 0, 0⟩ := by
  have h := r5r2_loop e (a := 2) (c := 0) (e := 0)
  simp only [Nat.zero_add] at h
  rw [show (2 * e + 2 : ℕ) = 2 + 2 * e from by ring]
  exact h

-- Steps from (2, 0, 2*e, 0, 0) to (0, 0, 2*e, 1, 0): R5, R3, R1, R1, R2
theorem phase2_steps (e : ℕ) : (⟨2, 0, 2 * e, 0, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, 2 * e, 1, 0⟩ := by
  step fm  -- R5: (1, 0, 2*e+2, 1, 0)
  step fm  -- R3: (1, 2, 2*e+2, 0, 1)
  step fm  -- R1: (1, 1, 2*e+1, 1, 1)
  step fm  -- R1: (1, 0, 2*e, 2, 1)
  step fm  -- R2: (0, 0, 2*e, 1, 0)
  finish

-- Compose R3R1R1 loop with R3 loop and R4 loop
theorem phase3_to_end (e : ℕ) : (⟨0, 0, 2 * e, 1, 0⟩ : Q) [fm]⊢* ⟨4 * e + 4, 0, 0, 0, 2 * e + 1⟩ := by
  -- R3+R1+R1 loop, e rounds: (0, 0, 2*e, 1, 0) ->* (0, 0, 0, e+1, e)
  rw [show (2 * e : ℕ) = 0 + 2 * e from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1r1_loop e (c := 0) (d := 0) (e := 0))
  -- Now at (0, 0, 0, e+1, e). R3 loop, e+1 rounds.
  rw [show 0 + e + 1 = e + 1 from by ring,
      show (0 : ℕ) + e = e from by ring,
      show (e + 1 : ℕ) = 0 + (e + 1) from by ring]
  apply stepStar_trans (r3_loop (e + 1) (b := 0) (d := 0) (e := e))
  -- Now at (0, 2*(e+1), 0, 0, 2*e+1). R4 loop.
  rw [show 0 + 2 * (e + 1) = 2 * (e + 1) from by ring,
      show e + (e + 1) = 2 * e + 1 from by ring,
      show (2 * (e + 1) : ℕ) = 0 + 2 * (e + 1) from by ring]
  apply stepStar_trans (r4_loop (2 * (e + 1)) (a := 0) (b := 0) (e := 2 * e + 1))
  ring_nf; finish

theorem main_trans (e : ℕ) : (⟨2 * e + 2, 0, 0, 0, e⟩ : Q) [fm]⊢⁺ ⟨4 * e + 4, 0, 0, 0, 2 * e + 1⟩ := by
  apply stepStar_stepPlus_stepPlus (phase1_to_phase2 e)
  apply stepPlus_stepStar_stepPlus (phase2_steps e)
  exact phase3_to_end e

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨8, 0, 0, 0, 3⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 2, 0, 0, 0, n⟩) 3
  intro n; exists (2 * n + 1)
  show (⟨2 * n + 2, 0, 0, 0, n⟩ : Q) [fm]⊢⁺ ⟨2 * (2 * n + 1) + 2, 0, 0, 0, 2 * n + 1⟩
  rw [show 2 * (2 * n + 1) + 2 = 4 * n + 4 from by ring]
  exact main_trans n
