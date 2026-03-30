import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1133: [5/6, 44/35, 49/2, 3/11, 242/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  1  0  0 -1
 1  0  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1133

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R3 repeated: drain a to d.
theorem a_drain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

-- R4 repeated: drain e to b.
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R2R1R1 chain: k rounds.
-- Each round: (0, B+2, C+1, D+1, E) → R2 → (2, B+2, C, D, E+1)
--             → R1 → (1, B+1, C+1, D, E+1) → R1 → (0, B, C+2, D, E+1)
-- After k rounds: b decreases by 2k, c increases by k, d decreases by k, e increases by k.
theorem r2r1r1_chain : ∀ k c d e, ⟨0, b + 2 * k, c + 1, d + k, e⟩ [fm]⊢*
    ⟨0, b, c + 1 + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show b + 2 * (k + 1) = b + 2 * k + 2 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    -- State: (0, b+2k+2, c+1, d+k+1, e). R2 fires (c+1>=1, d+k+1>=1).
    step fm  -- R2: (2, b+2k+2, c, d+k, e+1)
    -- Now need R1: a>=1,b>=1. a=2>=1. b=b+2k+2. Need to show b+2k+2 = _+1.
    rw [show b + 2 * k + 2 = (b + 2 * k + 1) + 1 from by ring]
    step fm  -- R1: (1, b+2k+1, c+1, d+k, e+1)
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm  -- R1: (0, b+2k, c+2, d+k, e+1)
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- R2 chain when b=0.
theorem r2_chain : ∀ k, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

-- The full transition.
theorem full_transition (n : ℕ) : ⟨2 * n + 3, 0, 0, n * n, 2 * n + 4⟩ [fm]⊢⁺
    ⟨2 * n + 5, 0, 0, (n + 1) * (n + 1), 2 * n + 6⟩ := by
  -- Phase 1: R3 drains a.
  rw [show 2 * n + 3 = 0 + (2 * n + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (a_drain (2 * n + 3) (a := 0) (d := n * n) (e := 2 * n + 4))
  -- Now at (0, 0, 0, n*n+2*(2n+3), 2n+4).
  -- Phase 2: R4 drains e to b.
  rw [show (2 * n + 4 : ℕ) = 0 + (2 * n + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * n + 4) (b := 0) (d := n * n + 2 * (2 * n + 3)) (e := 0))
  -- Now at (0, 2n+4, 0, n*n+4n+6, 0).
  -- Phase 3: R5 fires.
  rw [show n * n + 2 * (2 * n + 3) = (n * n + 4 * n + 5) + 1 from by ring,
      show (0 : ℕ) + (2 * n + 4) = (2 * n + 3) + 1 from by ring]
  step fm  -- R5: (1, 2n+4, 0, n*n+4n+5, 2)
  -- Phase 4: R1 fires.
  step fm  -- R1: (0, 2n+3, 1, n*n+4n+5, 2)
  -- Phase 5: R2R1R1 chain (n+1 rounds).
  -- Need to show the goal matches r2r1r1_chain pattern.
  -- Goal state: (0, 2n+3, 1, n*n+4n+5, 2).
  -- r2r1r1_chain needs (0, b+2*(n+1), c+1, d+(n+1), e).
  -- So b=1, 2*(n+1)=2n+2, b+2*(n+1)=2n+3. ✓
  -- c=0, c+1=1. ✓  d=n*n+3n+4, d+(n+1)=n*n+4n+5. ✓  e=2. ✓
  rw [show (2 * n + 3 : ℕ) = 1 + 2 * (n + 1) from by ring,
      show n * n + 4 * n + 5 = (n * n + 3 * n + 4) + (n + 1) from by ring]
  apply stepStar_trans (r2r1r1_chain (n + 1) (b := 1) 0 (n * n + 3 * n + 4) 2)
  -- After chain: (0, 1, n+2, n*n+3n+4, n+3).
  -- Phase 6: R2 + R1.
  rw [show 0 + 1 + (n + 1) = (n + 1) + 1 from by ring,
      show n * n + 3 * n + 4 = (n * n + 3 * n + 3) + 1 from by ring,
      show 2 + (n + 1) = n + 3 from by ring]
  step fm  -- R2: (2, 1, n+1, n*n+3n+3, n+4)
  step fm  -- R1: (1, 0, n+2, n*n+3n+3, n+4)
  -- Phase 7: R2 chain (n+2 times).
  rw [show n + 1 + 1 = 0 + (n + 2) from by ring,
      show n * n + 3 * n + 3 = (n + 1) * (n + 1) + (n + 2) from by ring]
  apply stepStar_trans (r2_chain (n + 2) (a := 1) (c := 0) (d := (n + 1) * (n + 1)) (e := n + 4))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 4⟩)
  · execute fm 10
  show ¬halts fm (2 * 0 + 3, 0, 0, 0 * 0, 2 * 0 + 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 0, n * n, 2 * n + 4⟩) 0
  intro n; exists (n + 1)
  exact full_transition n
