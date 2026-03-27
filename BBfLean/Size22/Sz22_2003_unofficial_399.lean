import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #399: [20/3, 9/35, 1/20, 343/2, 5/7]

Vector representation:
```
 2 -1  1  0
 0  2 -1 -1
-2  0 -1  0
-1  0  0  3
 0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_399

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a, b, c+1, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+2, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+3⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | _ => none

-- Phase 1: drain a to d when b=0, c=0
theorem a_to_d : ∀ k a d, ⟨a+k, 0, 0, d⟩ [fm]⊢* ⟨a, 0, 0, d+3*k⟩ := by
  intro k; induction k with
  | zero => intro a d; exists 0
  | succ k ih =>
    intro a d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 3))
    ring_nf; finish

-- Phase 2: start the climb from (0, 0, 0, d+2) to (0, 2, 0, d)
theorem start_climb (d : ℕ) : ⟨0, 0, 0, d+2⟩ [fm]⊢⁺ ⟨0, 2, 0, d⟩ := by
  execute fm 2

-- Phase 3: climb loop. From (4*k, 2, k, j) consume j to reach (4*(k+j), 2, k+j, 0)
theorem climb_loop : ∀ j k, ⟨4*k, 2, k, j⟩ [fm]⊢* ⟨4*(k+j), 2, k+j, 0⟩ := by
  intro j; induction j with
  | zero => intro k; ring_nf; exists 0
  | succ j ih =>
    intro k
    step fm; step fm; step fm
    show ⟨4*k+4, 2, k+1, j⟩ [fm]⊢* ⟨4*(k+(j+1)), 2, k+(j+1), 0⟩
    rw [show 4*k+4 = 4*(k+1) from by ring]
    apply stepStar_trans (ih (k+1))
    ring_nf; finish

-- Phase 4: finish the climb from (4*D, 2, D, 0)
-- Rule 1 twice: (4*D, 2, D, 0) -> (4*D+2, 1, D+1, 0) -> (4*D+4, 0, D+2, 0)
theorem finish_climb (D : ℕ) : ⟨4*D, 2, D, 0⟩ [fm]⊢⁺ ⟨4*D+4, 0, D+2, 0⟩ := by
  execute fm 2

-- Phase 5: drain a and c when b=0, d=0
-- Rule 3: (a+2, 0, c+1, 0) -> (a, 0, c, 0)
theorem drain_ac : ∀ k a, ⟨a+2*k, 0, k, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a; exists 0
  | succ k ih =>
    intro a
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring]
    step fm
    exact ih a

-- Main cycle: (2*n+2, 0, 0, 0) ⊢⁺ (12*n+8, 0, 0, 0) for all n
-- Actually we need (2*(n+1), 0, 0, 0) ⊢⁺ (2*(6*n+4), 0, 0, 0)
-- Let D = 6n+4. Then 6*(n+1)-2 = 6n+4 = D.
-- From (2*(n+1), 0, 0, 0):
--   Phase 1: -> (0, 0, 0, 6*(n+1)) = (0, 0, 0, 6n+6)
--   Phase 2: -> (0, 2, 0, 6n+4)  [since 6n+6 = (6n+4)+2]
--   Phase 3: -> (4*(6n+4), 2, 6n+4, 0)
--   Phase 4: -> (4*(6n+4)+4, 0, 6n+6, 0) = (24n+20, 0, 6n+6, 0)
--   Phase 5: -> (24n+20 - 2*(6n+6), 0, 0, 0) = (12n+8, 0, 0, 0)
theorem cycle (n : ℕ) : ⟨2*(n+1), 0, 0, 0⟩ [fm]⊢⁺ ⟨12*n+8, 0, 0, 0⟩ := by
  -- Phase 1: drain a
  apply stepStar_stepPlus_stepPlus
  · have h := a_to_d (2*(n+1)) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: start climb
  apply stepPlus_stepStar_stepPlus
  · rw [show 3 * (2 * (n + 1)) = (6*n+4)+2 from by ring]
    exact start_climb (6*n+4)
  -- Phase 3: climb loop
  apply stepStar_trans
  · have h := climb_loop (6*n+4) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 4: finish climb
  apply stepPlus_stepStar
  apply stepPlus_stepStar_stepPlus (finish_climb (6*n+4))
  -- Phase 5: drain
  show ⟨4*(6*n+4)+4, 0, (6*n+4)+2, 0⟩ [fm]⊢* ⟨12*n+8, 0, 0, 0⟩
  have h := drain_ac ((6*n+4)+2) (12*n+8)
  rw [show 12*n+8 + 2*((6*n+4)+2) = 4*(6*n+4)+4 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  -- From c₀ = (1, 0, 0, 0), execute to reach (2, 0, 0, 0)
  apply stepStar_not_halts_not_halts (c₂ := (⟨2, 0, 0, 0⟩ : Q))
  · execute fm 11
  -- Use progress_nonhalt_simple with C(n) = (2*(n+1), 0, 0, 0)
  -- cycle gives C(n) ⊢⁺ (12*n+8, 0, 0, 0)
  -- We need 12*n+8 = 2*(m+1) for some m, i.e., m = 6*n+3
  -- So C(n) ⊢⁺ C(6*n+3)
  exact progress_nonhalt_simple (fm := fm) (fun n ↦ (⟨2*(n+1), 0, 0, 0⟩ : Q)) 0
    (fun n ↦ ⟨6*n+3, by
      have h := cycle n
      show (⟨2*(n+1), 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨2*(6*n+3+1), 0, 0, 0⟩
      rw [show 2*(6*n+3+1) = 12*n+8 from by ring]
      exact h⟩)

end Sz22_2003_unofficial_399
