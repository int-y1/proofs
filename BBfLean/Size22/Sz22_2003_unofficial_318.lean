import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #318: [154/15, 3/7, 1/3, 125/2, 1/55, 7/5]

Vector representation:
```
 1 -1 -1  1  1
 0  1  0 -1  0
 0 -1  0  0  0
-1  0  3  0  0
 0  0 -1  0 -1
 0  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_318

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R1+R2 chain: (k, 1, c+j, 0, e) ->* (k+j, 1, c, 0, e+j)
theorem r1r2_chain : ∀ j k c e,
    ⟨k, 1, c + j, 0, e⟩ [fm]⊢* ⟨k + j, 1, c, 0, e + j⟩ := by
  intro j; induction j with
  | zero => intro k c e; exists 0
  | succ j ih =>
    intro k c e
    rw [show c + (j + 1) = (c + j) + 1 from by ring]
    step fm
    step fm
    rw [show k + (j + 1) = (k + 1) + j from by ring,
        show e + (j + 1) = (e + 1) + j from by ring]
    exact ih (k + 1) c (e + 1)

-- R4 chain: (a, 0, c, 0, e) ->* (0, 0, c+3*a, 0, e)
theorem r4_chain : ∀ a c e,
    ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 3 * a, 0, e⟩ := by
  intro a; induction a with
  | zero => intro c e; simp; exists 0
  | succ a ih =>
    intro c e
    step fm
    rw [show c + 3 * (a + 1) = (c + 3) + 3 * a from by ring]
    exact ih (c + 3) e

-- R5 chain: (0, 0, c+e, 0, e) ->* (0, 0, c, 0, 0)
theorem r5_chain : ∀ e c,
    ⟨0, 0, c + e, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro e; induction e with
  | zero => intro c; exists 0
  | succ e ih =>
    intro c
    rw [show c + (e + 1) = (c + e) + 1 from by ring]
    step fm
    exact ih c

-- Main transition: (0, 0, c+2, 0, 0) ->+ (0, 0, 2*c+2, 0, 0)
theorem main_trans (c : ℕ) : ⟨0, 0, c + 2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 2, 0, 0⟩ := by
  -- Phase 1+2: R6 then R2
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm  -- R6
  step fm  -- R2
  -- Phase 3: R1+R2 chain: (0, 1, c+1, 0, 0) ->* (c+1, 1, 0, 0, c+1)
  rw [show c + 1 = 0 + (c + 1) from by ring]
  apply stepStar_trans (r1r2_chain (c + 1) 0 0 0)
  simp only [Nat.zero_add]
  -- Phase 4: R3
  step fm
  -- Phase 5: R4 chain: (c+1, 0, 0, 0, c+1) ->* (0, 0, 3*(c+1), 0, c+1)
  apply stepStar_trans (r4_chain (c + 1) 0 (c + 1))
  -- Phase 6: R5 chain
  rw [show 0 + 3 * (c + 1) = 2 * c + 2 + (c + 1) from by ring]
  exact r5_chain (c + 1) (2 * c + 2)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, n + 3, 0, 0⟩) 0
  intro n
  refine ⟨2 * n + 1, ?_⟩
  rw [show n + 3 = (n + 1) + 2 from by ring,
      show (2 * n + 1) + 3 = 2 * (n + 1) + 2 from by ring]
  exact main_trans (n + 1)

end Sz22_2003_unofficial_318
