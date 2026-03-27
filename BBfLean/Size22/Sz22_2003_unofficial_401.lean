import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #401: [20/3, 9/35, 1/20, 49/2, 9/7]

Vector representation:
```
 2 -1  1  0
 0  2 -1 -1
-2  0 -1  0
-1  0  0  2
 0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_401

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a, b, c+1, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+2, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | _ => none

-- R1 chain: consume b, grow a and c
-- (a, b+k, c, d) ->* (a+2*k, b, c+k, d)
theorem r1_chain : ∀ k, ∀ a b c d,
    ⟨a, b+k, c, d⟩ [fm]⊢* ⟨a+2*k, b, c+k, d⟩ := by
  intro k; induction k with
  | zero => intro a b c d; exists 0
  | succ k ih =>
    intro a b c d
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- Growth step: R2 then R1x2
-- (a, 0, c+1, d+1) -> R2 -> (a, 2, c, d) -> R1x2 -> (a+4, 0, c+2, d)
theorem growth_step : ∀ a c d,
    ⟨a, 0, c+1, d+1⟩ [fm]⊢* ⟨a+4, (0 : ℕ), c+2, d⟩ := by
  intro a c d
  -- R2: (a, 0, c+1, d+1) -> (a, 2, c, d)
  step fm
  -- R1x2: (a, 2, c, d) -> (a+4, 0, c+2, d)
  step fm; step fm
  ring_nf; finish

-- Growth loop: (R2+R1x2) repeated k times
-- Starting from (a, 0, c+1, d+k), arrive at (a+4*k, 0, c+k+1, d)
theorem growth_loop : ∀ k, ∀ a c d,
    ⟨a, 0, c+1, d+k⟩ [fm]⊢* ⟨a+4*k, (0 : ℕ), c+k+1, d⟩ := by
  intro k; induction k with
  | zero => intro a c d; ring_nf; exists 0
  | succ k ih =>
    intro a c d
    -- Rewrite d+k+1 as d+(k+1) then as (d+k)+1 ... but we need c+1 and (d+k)+1
    -- State: (a, 0, c+1, d+(k+1))
    -- = (a, 0, c+1, (d+k)+1) but wait, c+1 is already there
    -- growth_step: (a, 0, c+1, (d+k)+1) -> (a+4, 0, c+2, d+k)
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (growth_step a c (d + k))
    -- Now: (a+4, 0, c+2, d+k)
    -- = (a+4, 0, (c+1)+1, d+k)
    -- ih: (a+4, 0, (c+1)+1, d+k) ->* (a+4+4*k, 0, (c+1)+k+1, d)
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 4) (c + 1) d)
    ring_nf; finish

-- R3 chain: consume a (by 2) and c (by 1)
-- (a+2*k, 0, c+k, 0) ->* (a, 0, c, 0)
theorem r3_chain : ∀ k, ∀ a c,
    ⟨a+2*k, 0, c+k, 0⟩ [fm]⊢* ⟨a, (0 : ℕ), c, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 1 + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R4 chain: consume a, grow d
-- (a+k, 0, 0, d) ->* (a, 0, 0, d+2*k)
theorem r4_chain : ∀ k, ∀ a d,
    ⟨a+k, 0, 0, d⟩ [fm]⊢* ⟨a, (0 : ℕ), 0, d+2*k⟩ := by
  intro k; induction k with
  | zero => intro a d; exists 0
  | succ k ih =>
    intro a d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Main transition: (0, 0, 0, d+2) ⊢⁺ (0, 0, 0, 4*d+4)
theorem main_trans (d : ℕ) :
    ⟨0, 0, 0, d+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*d+4⟩ := by
  -- R5: (0, 0, 0, (d+1)+1) -> (0, 2, 0, d+1)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2, 0, d+1⟩)
  · rw [show d + 2 = (d + 1) + 1 from by ring]; simp [fm]
  -- R1x2: (0, 2, 0, d+1) -> (4, 0, 2, d+1)
  apply stepStar_trans (c₂ := ⟨4, 0, 2, d+1⟩)
  · step fm; step fm; ring_nf; finish
  -- Growth loop (d+1) times: (4, 0, 2, d+1) ->* (4+4*(d+1), 0, d+3, 0)
  apply stepStar_trans (c₂ := ⟨4+4*(d+1), 0, d+3, 0⟩)
  · have h := growth_loop (d+1) 4 1 0
    rw [show (1 : ℕ) + 1 = 2 from by ring,
        show 0 + (d + 1) = d + 1 from by ring,
        show (1 : ℕ) + (d + 1) + 1 = d + 3 from by ring] at h
    exact h
  -- R3 chain (d+3) times: (4+4*(d+1), 0, d+3, 0) -> (2*d+2, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨2*d+2, 0, 0, 0⟩)
  · have h := r3_chain (d+3) (2*d+2) 0
    rw [show (0 : ℕ) + (d + 3) = d + 3 from by ring,
        show 2 * d + 2 + 2 * (d + 3) = 4 + 4 * (d + 1) from by ring] at h
    exact h
  -- R4 chain (2*d+2) times: (2*d+2, 0, 0, 0) -> (0, 0, 0, 4*d+4)
  have h := r4_chain (2*d+2) 0 0
  rw [show (0 : ℕ) + (2 * d + 2) = 2 * d + 2 from by ring,
      show (0 : ℕ) + 2 * (2 * d + 2) = 4 * d + 4 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm) (fun c => ∃ d, c = (⟨0, 0, 0, d + 2⟩ : Q))
  · intro c ⟨d, hd⟩
    subst hd
    exact ⟨⟨0, 0, 0, 4*d+4⟩, ⟨4*d+2, rfl⟩, main_trans d⟩
  · exact ⟨0, rfl⟩

end Sz22_2003_unofficial_401
