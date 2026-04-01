import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1596: [77/15, 12/7, 1/3, 25/2, 1/55, 3/5]

Vector representation:
```
 0 -1 -1  1  1
 2  1  0 -1  0
 0 -1  0  0  0
-1  0  2  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1596

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: convert a to c.
theorem r4_chain : ∀ a, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * a, 0, e⟩ := by
  intro a; induction' a with a ih generalizing c
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 2))
    rw [show c + 2 + 2 * a = c + 2 * (a + 1) from by ring]; exists 0

-- R5 chain: drain e paired with c.
theorem r5_chain : ∀ k, ⟨0, 0, c + k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    exact ih (c := c)

-- R1+R2 interleaved chain.
theorem r1r2_chain : ∀ k, ⟨a, 1, k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 1, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · simp; exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; exists 0

-- R6 + R1R2 chain + R3: (0, 0, c+1, 0, 0) →⁺ (2*c, 0, 0, 0, c)
theorem r6_chain : ⟨0, 0, c + 1, 0, 0⟩ [fm]⊢⁺ ⟨2 * c, 0, 0, 0, c⟩ := by
  step fm  -- R6: (0, 1, c, 0, 0)
  apply stepStar_trans (r1r2_chain c (a := 0) (e := 0))
  simp only [Nat.zero_add]
  show ⟨2 * c, 1, 0, 0, c⟩ [fm]⊢* ⟨2 * c, 0, 0, 0, c⟩
  step fm  -- R3
  exists 0

-- Full transition: (2*(n+1), 0, 0, 0, n+1) →⁺ (6*n+4, 0, 0, 0, 3*n+2)
theorem main_trans : ⟨2 * n + 2, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨6 * n + 4, 0, 0, 0, 3 * n + 2⟩ := by
  -- Phase 1: R4 chain: (2n+2, 0, 0, 0, n+1) →* (0, 0, 4n+4, 0, n+1)
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * n + 2) (c := 0) (e := n + 1))
  rw [show 0 + 2 * (2 * n + 2) = (3 * n + 3) + (n + 1) from by ring]
  -- Phase 2: R5 chain: (0, 0, (3n+3)+(n+1), 0, n+1) →* (0, 0, 3n+3, 0, 0)
  apply stepStar_stepPlus_stepPlus (r5_chain (n + 1) (c := 3 * n + 3))
  -- Phase 3+4: R6 + R1R2 + R3: (0, 0, 3n+3, 0, 0) →⁺ (6n+4, 0, 0, 0, 3n+2)
  rw [show 3 * n + 3 = (3 * n + 2) + 1 from by ring]
  rw [show (6 * n + 4 : ℕ) = 2 * (3 * n + 2) from by ring]
  exact r6_chain

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 2, 0, 0, 0, n + 1⟩) 0
  intro n; exists 3 * n + 1
  show ⟨2 * n + 2, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨2 * (3 * n + 1) + 2, 0, 0, 0, (3 * n + 1) + 1⟩
  rw [show 2 * (3 * n + 1) + 2 = 6 * n + 4 from by ring,
      show (3 * n + 1) + 1 = 3 * n + 2 from by ring]
  exact main_trans
