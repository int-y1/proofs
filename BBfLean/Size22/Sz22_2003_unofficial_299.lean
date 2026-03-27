import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #299: [15/2, 110/21, 1/3, 49/5, 1/77, 3/7]

Vector representation:
```
-1  1  1  0  0
 1 -1  1 -1  1
 0 -1  0  0  0
 0  0 -1  2  0
 0  0  0 -1 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_299

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R2+R1 pair: (0, 1, c, d+1, e) -> (0, 1, c+2, d, e+1)
-- R2: (0, 1, c, d+1, e) -> (1, 0, c+1, d, e+1)
-- R1: (1, 0, c+1, d, e+1) -> (0, 1, c+2, d, e+1)
theorem r2r1_pair (c d e : ℕ) :
    ⟨0, 1, c, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), 1, c + 2, d, e + 1⟩ := by
  step fm; step fm; finish

-- R2+R1 loop: (0, 1, 0, k, 0) -> (0, 1, 2*k, 0, k)
theorem r2r1_loop : ∀ k c d e,
    ⟨0, 1, c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), 1, c + 2 * k, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro c d e; simp; exists 0
  | succ k ih =>
    intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (r2r1_pair c (d + k) e)
    rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih (c + 2) d (e + 1)

-- R4 drain c: (0, 0, c, d, e) -> (0, 0, 0, d + 2*c, e)
theorem r4_drain : ∀ k d e,
    ⟨0, 0, k, d, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, d + 2 * k, e⟩ := by
  intro k; induction k with
  | zero => intro d e; simp; exists 0
  | succ k ih =>
    intro d e; step fm
    rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    exact ih (d + 2) e

-- R5 drain: (0, 0, 0, d + k, k) -> (0, 0, 0, d, 0)
theorem r5_drain : ∀ k d,
    ⟨0, 0, 0, d + k, k⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intro d; simp; exists 0
  | succ k ih =>
    intro d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; exact ih d

-- Main transition: (0, 0, 0, d+2, 0) ->+ (0, 0, 0, 3*d+3, 0)
theorem main_trans (d : ℕ) :
    ⟨0, 0, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 3 * d + 3, 0⟩ := by
  -- R6: (0, 0, 0, d+2, 0) -> (0, 1, 0, d+1, 0)
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm
  -- R2+R1 loop: (0, 1, 0, d+1, 0) -> (0, 1, 2*(d+1), 0, d+1)
  rw [show (d + 1 : ℕ) = 0 + (d + 1) from by ring]
  apply stepStar_trans (r2r1_loop (d + 1) 0 0 0)
  rw [show 0 + 2 * (d + 1) = 2 * (d + 1) from by ring,
      show 0 + (d + 1) = d + 1 from by ring]
  -- R3: (0, 1, 2*(d+1), 0, d+1) -> (0, 0, 2*(d+1), 0, d+1)
  step fm
  -- R4 drain c: (0, 0, 2*(d+1), 0, d+1) -> (0, 0, 0, 4*(d+1), d+1)
  apply stepStar_trans (r4_drain (2 * (d + 1)) 0 (d + 1))
  rw [show 0 + 2 * (2 * (d + 1)) = 4 * (d + 1) from by ring]
  -- R5 drain: (0, 0, 0, 4*(d+1), d+1) -> (0, 0, 0, 3*(d+1), 0)
  rw [show 4 * (d + 1) = 3 * (d + 1) + (d + 1) from by ring]
  apply stepStar_trans (r5_drain (d + 1) (3 * (d + 1)))
  rw [show 3 * (d + 1) = 3 * d + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · unfold c₀; execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, 0⟩) 0
  intro n; exact ⟨3 * n + 1, main_trans n⟩

end Sz22_2003_unofficial_299
