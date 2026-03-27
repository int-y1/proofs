import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #234: [11/105, 20/3, 3/22, 35/2, 9/5]

Vector representation:
```
 0 -1 -1 -1  1
 2 -1  1  0  0
-1  1  0  0 -1
-1  0  1  1  0
 0  2 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_234

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- Drain k rounds: R5+R1+R1 repeated
-- (0, 0, C+3k, D+2k, E) ->* (0, 0, C, D, E+2k)
theorem drain : ∀ k C D E,
    ⟨0, 0, C + 3 * k, D + 2 * k, E⟩ [fm]⊢* ⟨(0 : ℕ), 0, C, D, E + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro C D E; simp; exists 0
  | succ k ih =>
    intro C D E
    rw [show C + 3 * (k + 1) = (C + 3 * k + 2) + 1 from by ring]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show C + 3 * k + 2 = (C + 3 * k + 1) + 1 from by ring,
        show D + 2 * (k + 1) = (D + 2 * k + 1) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show C + 3 * k + 1 = (C + 3 * k) + 1 from by ring,
        show D + 2 * k + 1 = (D + 2 * k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih C D (E + 1 + 1))
    ring_nf; finish

-- Last drain: R5 + R1 when d=1
-- (0, 0, C+2, D+1, E) ->* (0, 1, C, D, E+1)
theorem last_drain (C D E : ℕ) :
    ⟨0, 0, C + 2, D + 1, E⟩ [fm]⊢* ⟨(0 : ℕ), 1, C, D, E + 1⟩ := by
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show C + 1 = C + 1 from by ring]
  step fm
  finish

-- Pump pairs: R3+R2 repeated k times
-- Each pair: (a+1, 0, c, 0, e+1) ->R3 (a, 1, c, 0, e) ->R2 (a+2, 0, c+1, 0, e)
-- Net per pair: a+1, c+1, e-1
-- (A+1, 0, C, 0, k) ->* (A+k+1, 0, C+k, 0, 0)
theorem pump_pairs : ∀ k A C,
    ⟨A + 1, 0, C, 0, k⟩ [fm]⊢* ⟨A + k + 1, (0 : ℕ), C + k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro A C; simp; exists 0
  | succ k ih =>
    intro A C
    rw [show (k + 1) = k + 1 from by ring]
    -- R3: (A+1, 0, C, 0, k+1) -> (A, 1, C, 0, k)
    step fm
    -- R2: (A, 1, C, 0, k) -> (A+2, 0, C+1, 0, k)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    -- Now at (A+2, 0, C+1, 0, k) = ((A+1)+1, 0, C+1, 0, k)
    rw [show A + 2 = (A + 1) + 1 from by ring]
    apply stepStar_trans (ih (A + 1) (C + 1))
    ring_nf; finish

-- Full pump: (0, 1, C, 0, E+1) ->* (E+3, 0, C+E+2, 0, 0)
-- R2: (0, 0+1, C, 0, E+1) -> (2, 0, C+1, 0, E+1) = (1+1, 0, C+1, 0, E+1)
-- pump_pairs E+1: (1+1, 0, C+1, 0, E+1) -> (1+E+1+1, 0, C+1+E+1, 0, 0)
-- = (E+3, 0, C+E+2, 0, 0)
theorem pump (C E : ℕ) :
    ⟨0, 1, C, 0, E + 1⟩ [fm]⊢* ⟨E + 3, (0 : ℕ), C + E + 2, 0, 0⟩ := by
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show E + 1 = E + 1 from by ring]
  apply stepStar_trans (pump_pairs (E + 1) 1 (C + 1))
  ring_nf; finish

-- R4 chain: (k, 0, C, D, 0) ->* (0, 0, C+k, D+k, 0)
theorem r4_chain : ∀ k C D,
    ⟨k, 0, C, D, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, C + k, D + k, 0⟩ := by
  intro k; induction k with
  | zero => intro C D; simp; exists 0
  | succ k ih =>
    intro C D
    step fm
    apply stepStar_trans (ih (C + 1) (D + 1))
    ring_nf; finish

-- Main transition
-- state (n, C) = (0, 0, C + 3*(n+1) + 2, 2*(n+1) + 1, 0)
-- Transition: (n, C) -> (n+1, C+n+1)
-- target state: (0, 0, (C+n+1) + 3*(n+2) + 2, 2*(n+2) + 1, 0)
-- = (0, 0, C + 4n + 9, 2n + 5, 0)
--
-- Phases:
-- 1. drain (n+1) rounds: c -= 3(n+1), d -= 2(n+1), e += 2(n+1)
--    (0, 0, C+3(n+1)+2, 2(n+1)+1, 0) -> (0, 0, C+2, 1, 2(n+1))
-- 2. last_drain: (0, 0, C+2, 0+1, 2(n+1)) -> (0, 1, C, 0, 2(n+1)+1)
-- 3. pump: (0, 1, C, 0, 2(n+1)+1) -> (2(n+1)+3, 0, C+2(n+1)+2, 0, 0)
--    = (2n+5, 0, C+2n+4, 0, 0)
-- 4. r4_chain: (2n+5, 0, C+2n+4, 0, 0) -> (0, 0, C+4n+9, 2n+5, 0)
theorem main_trans (n C : ℕ) :
    ⟨0, 0, C + 3 * (n + 1) + 2, 2 * (n + 1) + 1, 0⟩ [fm]⊢⁺
    ⟨0, 0, (C + n + 1) + 3 * (n + 2) + 2, 2 * (n + 2) + 1, 0⟩ := by
  -- First R5 step (to get ⊢⁺) using step macro
  rw [show C + 3 * (n + 1) + 2 = (C + 3 * n + 4) + 1 from by ring]
  step fm
  -- After R5: (0, 2, C+3n+4, 2(n+1)+1, 0)
  -- Now R1 (first of two)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show C + 3 * n + 4 = (C + 3 * n + 3) + 1 from by ring,
      show 2 * (n + 1) + 1 = (2 * n + 2) + 1 from by ring]
  step fm
  -- After R1: (0, 1, C+3n+3, 2n+2, E+1)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show C + 3 * n + 3 = (C + 3 * n + 2) + 1 from by ring,
      show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  -- After R1: (0, 0, C+3n+2, 2n+1, 0+1+1)
  -- = (0, 0, (C+2)+3n, 1+2n, 2) matching drain form
  rw [show C + 3 * n + 2 = (C + 2) + 3 * n from by ring,
      show 2 * n + 1 = 1 + 2 * n from by ring]
  -- Phase 1 (remaining): drain n rounds
  apply stepStar_trans (drain n (C + 2) 1 (0 + 1 + 1))
  -- After drain: (0, 0, C+2, 1, 0+1+1+2n)
  -- Phase 2: last_drain
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (last_drain C 0 (0 + 1 + 1 + 2 * n))
  -- After last_drain: (0, 1, C, 0, 0+1+1+2n+1)
  -- Phase 3: pump
  rw [show 0 + 1 + 1 + 2 * n + 1 = 2 * n + 2 + 1 from by ring]
  apply stepStar_trans (pump C (2 * n + 2))
  -- After pump: (2n+2+3, 0, C+2n+2+2, 0, 0) = (2n+5, 0, C+2n+4, 0, 0)
  -- Phase 4: r4_chain
  rw [show 2 * n + 2 + 3 = 2 * n + 5 from by ring,
      show C + (2 * n + 2) + 2 = C + 2 * n + 4 from by ring]
  apply stepStar_trans (r4_chain (2 * n + 5) (C + 2 * n + 4) 0)
  rw [show C + 2 * n + 4 + (2 * n + 5) = (C + n + 1) + 3 * (n + 2) + 2 from by ring,
      show 0 + (2 * n + 5) = 2 * (n + 2) + 1 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 8, 5, 0⟩) (by execute fm 26)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, C⟩ ↦ ⟨0, 0, C + 3 * (n + 1) + 2, 2 * (n + 1) + 1, 0⟩) ⟨1, 0⟩
  intro ⟨n, C⟩
  exact ⟨⟨n + 1, C + n + 1⟩, main_trans n C⟩

end Sz22_2003_unofficial_234
