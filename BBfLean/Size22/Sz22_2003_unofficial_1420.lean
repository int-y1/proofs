import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1420: [7/15, 18/77, 11/3, 5/121, 147/2]

Vector representation:
```
 0 -1 -1  1  0
 1  2  0 -1 -1
 0 -1  0  0  1
 0  0  1  0 -2
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1420

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R3/R2 chain: k rounds. Each round: R3 then R2.
-- In each round b decreases by 1 (R3) then increases by 2 (R2), net +1.
-- We keep b+1 visible to ensure pattern matching works.
-- From (a, b+1, 0, d+1, 0):
--   R3 -> (a, b, 0, d+1, 1)
--   R2 -> (a+1, b+2, 0, d, 0) = (a+1, (b+1)+1, 0, d, 0)
-- So after k rounds: (a+k, b+k+1, 0, d+1-k, 0) when d+1 >= k.
-- Parameterize: start (a, b+1, 0, d+k, 0), end (a+k, b+k+1, 0, d, 0)
theorem r3r2_chain : ∀ k, ∀ a b d,
    ⟨a, b + 1, (0 : ℕ), d + k, (0 : ℕ)⟩ [fm]⊢* ⟨a + k, b + k + 1, (0 : ℕ), d, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring]
    -- State: (a, b+1, 0, d+k+1, 0)
    -- Take one R3/R2 round first, then apply ih
    step fm  -- R3: (a, b, 0, d+k+1, 1)
    rw [show d + k + 1 = (d + k) + 1 from by ring]
    step fm  -- R2: (a+1, b+2, 0, d+k, 0)
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 1) d)
    rw [show a + 1 + k = a + (k + 1) from by ring,
        show b + 1 + k + 1 = b + (k + 1) + 1 from by ring]
    finish

-- R3 chain: move b to e
theorem b_to_e : ∀ k, ∀ a b,
    ⟨a, b + k, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩ [fm]⊢* ⟨a, b, (0 : ℕ), (0 : ℕ), k⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    apply stepStar_trans (ih a (b + 1))
    step fm
    rw [show k + 1 = k + 1 from rfl]
    finish

-- R4 chain: pair up e into c
theorem e_to_c : ∀ k, ∀ a e,
    ⟨a, (0 : ℕ), (0 : ℕ), (0 : ℕ), e + 2 * k⟩ [fm]⊢* ⟨a, (0 : ℕ), k, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    apply stepStar_trans (ih a (e + 2))
    step fm
    finish

-- Drain: R5 then R1, consuming c and accumulating d
theorem drain : ∀ k, ∀ a d,
    ⟨a + k, (0 : ℕ), k, d, (0 : ℕ)⟩ [fm]⊢* ⟨a, (0 : ℕ), (0 : ℕ), d + 3 * k, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm  -- R5: (a+k, 1, k+1, d+2, 0)
    step fm  -- R1: (a+k, 0, k, d+3, 0)
    apply stepStar_trans (ih a (d + 3))
    rw [show d + 3 + 3 * k = d + 3 * (k + 1) from by ring]
    finish

-- Odd phase 4 init: 5 steps from (a+1, 0, c+3, 0, 1) to (a+1, 0, c, 4, 0)
theorem odd_init (a c : ℕ) :
    ⟨a + 1, (0 : ℕ), c + 3, (0 : ℕ), (1 : ℕ)⟩ [fm]⊢*
    ⟨a + 1, (0 : ℕ), c, (4 : ℕ), (0 : ℕ)⟩ := by
  step fm  -- R5: (a, 1, c+3, 2, 1)
  step fm  -- R1: (a, 0, c+2, 3, 1)
  step fm  -- R2: (a+1, 2, c+2, 2, 0)
  step fm  -- R1: (a+1, 1, c+1, 3, 0)
  step fm  -- R1: (a+1, 0, c, 4, 0)
  finish

-- Main transition for even d₀ (B odd, odd phase):
-- (a+1, 0, 0, 2k+6, 0) ->+ (a+k+7, 0, 0, 3k+7, 0)
theorem main_even (a k : ℕ) :
    ⟨a + 1, (0 : ℕ), (0 : ℕ), 2 * k + 6, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨a + k + 7, (0 : ℕ), (0 : ℕ), 3 * k + 7, (0 : ℕ)⟩ := by
  -- Phase 1: 3 init steps
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨a + 1, 0, 0, 2 * k + 6, 0⟩ : Q) [fm]⊢ ⟨a, 1, 0, 2 * k + 8, 0⟩)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨a, 1, 0, 2 * k + 8, 0⟩ : Q) [fm]⊢ ⟨a, 0, 0, 2 * k + 8, 1⟩))
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨a, 0, 0, 2 * k + 8, 1⟩ : Q) [fm]⊢ ⟨a + 1, 2, 0, 2 * k + 7, 0⟩))
  -- Phase 2: R3/R2 chain, 2k+7 rounds
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * k + 7 = 0 + (2 * k + 7) from by ring]
  apply stepStar_trans (r3r2_chain (2 * k + 7) (a + 1) 1 0)
  rw [show a + 1 + (2 * k + 7) = a + 2 * k + 8 from by ring,
      show 1 + (2 * k + 7) + 1 = 2 * k + 9 from by ring]
  -- State: (a+2k+8, 2k+9, 0, 0, 0)
  -- Phase 3: b_to_e
  rw [show (2 * k + 9 : ℕ) = 0 + (2 * k + 9) from by ring]
  apply stepStar_trans (b_to_e (2 * k + 9) (a + 2 * k + 8) 0)
  -- Phase 4: e_to_c with odd e. 2k+9 = 1 + 2*(k+4)
  rw [show (2 * k + 9 : ℕ) = 1 + 2 * (k + 4) from by ring]
  apply stepStar_trans (e_to_c (k + 4) (a + 2 * k + 8) 1)
  -- State: (a+2k+8, 0, k+4, 0, 1)
  -- Phase 5: odd_init
  rw [show (k + 4 : ℕ) = (k + 1) + 3 from by ring,
      show a + 2 * k + 8 = (a + 2 * k + 7) + 1 from by ring]
  apply stepStar_trans (odd_init (a + 2 * k + 7) (k + 1))
  -- State: (a+2k+8, 0, k+1, 4, 0)
  rw [show (a + 2 * k + 7) + 1 = (a + k + 7) + (k + 1) from by ring]
  apply stepStar_trans (drain (k + 1) (a + k + 7) 4)
  rw [show 4 + 3 * (k + 1) = 3 * k + 7 from by ring]
  finish

-- Main transition for odd d₀ (B even, even phase):
-- (a+1, 0, 0, 2k+7, 0) ->+ (a+k+4, 0, 0, 3k+15, 0)
theorem main_odd (a k : ℕ) :
    ⟨a + 1, (0 : ℕ), (0 : ℕ), 2 * k + 7, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨a + k + 4, (0 : ℕ), (0 : ℕ), 3 * k + 15, (0 : ℕ)⟩ := by
  -- Phase 1: 3 init steps
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨a + 1, 0, 0, 2 * k + 7, 0⟩ : Q) [fm]⊢ ⟨a, 1, 0, 2 * k + 9, 0⟩)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨a, 1, 0, 2 * k + 9, 0⟩ : Q) [fm]⊢ ⟨a, 0, 0, 2 * k + 9, 1⟩))
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨a, 0, 0, 2 * k + 9, 1⟩ : Q) [fm]⊢ ⟨a + 1, 2, 0, 2 * k + 8, 0⟩))
  -- Phase 2: R3/R2 chain, 2k+8 rounds
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * k + 8 = 0 + (2 * k + 8) from by ring]
  apply stepStar_trans (r3r2_chain (2 * k + 8) (a + 1) 1 0)
  rw [show a + 1 + (2 * k + 8) = a + 2 * k + 9 from by ring,
      show 1 + (2 * k + 8) + 1 = 2 * k + 10 from by ring]
  -- Phase 3: b_to_e
  rw [show (2 * k + 10 : ℕ) = 0 + (2 * k + 10) from by ring]
  apply stepStar_trans (b_to_e (2 * k + 10) (a + 2 * k + 9) 0)
  -- Phase 4: e_to_c, 2k+10 = 0 + 2*(k+5)
  rw [show (2 * k + 10 : ℕ) = 0 + 2 * (k + 5) from by ring]
  apply stepStar_trans (e_to_c (k + 5) (a + 2 * k + 9) 0)
  -- State: (a+2k+9, 0, k+5, 0, 0)
  -- Phase 5: drain k+5 rounds
  rw [show a + 2 * k + 9 = (a + k + 4) + (k + 5) from by ring]
  apply stepStar_trans (drain (k + 5) (a + k + 4) 0)
  rw [show 0 + 3 * (k + 5) = 3 * k + 15 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 6, 0⟩) (by execute fm 26)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + 1, (0 : ℕ), (0 : ℕ), d + 6, (0 : ℕ)⟩)
  · intro q ⟨a, d, hq⟩
    subst hq
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      refine ⟨⟨a + k + 7, 0, 0, 3 * k + 7, 0⟩,
             ⟨a + k + 6, 3 * k + 1, by ring_nf⟩, ?_⟩
      have h := main_even a k
      convert h using 2; ring_nf
    · subst hk
      refine ⟨⟨a + k + 4, 0, 0, 3 * k + 15, 0⟩,
             ⟨a + k + 3, 3 * k + 9, by ring_nf⟩, ?_⟩
      have h := main_odd a k
      convert h using 2
  · exact ⟨1, 0, by ring_nf⟩

end Sz22_2003_unofficial_1420
