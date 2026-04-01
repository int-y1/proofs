import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1251: [5/6, 77/2, 52/35, 3/13, 65/11]

Vector representation:
```
-1 -1  1  0  0  0
-1  0  0  1  1  0
 2  0 -1 -1  0  1
 0  1  0  0  0 -1
 0  0  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1251

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | _ => none

-- R4 repeated: drain f to b
theorem f_to_b : ∀ k b d e f, ⟨(0 : ℕ), b, 0, d, e, f + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih
  · intro b d e f; exists 0
  · intro b d e f
    rw [Nat.add_succ f k]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

-- R1,R1,R3 chain: k rounds from (2, 2k, c, k, e, f) to (2, 0, c+k, 0, e, f+k)
theorem r1r1r3_chain : ∀ k, ∀ c e f, ⟨(2 : ℕ), 2 * k, c, k, e, f⟩ [fm]⊢* ⟨(2 : ℕ), 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih
  · intro c e f; simp; exists 0
  · intro c e f
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e (f + 1))
    rw [show c + 1 + k = c + (k + 1) from by ring,
        show f + 1 + k = f + (k + 1) from by ring]
    finish

-- R2,R2,R3 chain: k rounds from (2, 0, c+k, d, e, f) to (2, 0, c, d+k, e+2*k, f+k)
theorem r2r2r3_chain : ∀ k, ∀ c d e f, ⟨(2 : ℕ), (0 : ℕ), c + k, d, e, f⟩ [fm]⊢* ⟨(2 : ℕ), (0 : ℕ), c, d + k, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih
  · intro c d e f; simp; exists 0
  · intro c d e f
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e f)
    rw [show c + 1 = c + 1 from rfl]
    step fm
    step fm
    rw [show c + 1 = c + 1 from rfl,
        show d + k + 1 + 1 = (d + k + 1) + 1 from by ring]
    step fm
    rw [show d + k + 1 = d + (k + 1) from by ring,
        show e + 2 * k + 1 + 1 = e + 2 * (k + 1) from by ring,
        show f + k + 1 = f + (k + 1) from by ring]
    finish

-- Main transition: C(n) ⊢⁺ C(n+1)
-- C(n) = (0, 0, 0, n+1, n*n+1, 2*n)
theorem main_transition (n : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, n + 1, n * n + 1, 2 * n⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, n + 2, n * n + 2 * n + 2, 2 * n + 2⟩ := by
  -- Phase 1: drain f to b: (0, 0, 0, n+1, n²+1, 2n) -> (0, 2n, 0, n+1, n²+1, 0)
  rw [show 2 * n = 0 + 2 * n from by ring]
  apply stepStar_stepPlus_stepPlus (f_to_b (2 * n) 0 (n + 1) (n * n + 1) 0)
  rw [show (0 : ℕ) + 2 * n = 2 * n from by ring]
  -- Phase 2: R5 step
  rw [show n * n + 1 = n * n + 0 + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 2 * n, 0, n + 1, n * n + 0 + 1, 0⟩ : Q) [fm]⊢
      ⟨0, 2 * n, 1, n + 1, n * n + 0, 1⟩)
  -- State: (0, 2n, 1, n+1, n², 1)
  -- Phase 3: R3 step
  rw [show n + 1 = n + 1 from rfl]
  apply stepStar_trans
    (step_stepStar (by simp [fm] : (⟨0, 2 * n, 1, n + 1, n * n + 0, 1⟩ : Q) [fm]⊢
      ⟨2, 2 * n, 0, n, n * n + 0, 2⟩))
  -- State: (2, 2n, 0, n, n², 2)
  -- Phase 4: r1r1r3 chain: (2, 2n, 0, n, n², 2) -> (2, 0, n, 0, n², n+2)
  apply stepStar_trans (r1r1r3_chain n 0 (n * n + 0) 2)
  -- State: (2, 0, n, 0, n², n+2)
  -- Phase 5: r2r2r3 chain: (2, 0, n, 0, n², n+2) -> (2, 0, 0, n, n²+2n, 2n+2)
  rw [show (0 : ℕ) + n = 0 + n from rfl]
  apply stepStar_trans (r2r2r3_chain n 0 0 (n * n + 0) ((2 : ℕ) + n))
  -- State: (2, 0, 0, n, n²+2n, 2n+2)
  -- Phase 6: R2, R2 to finish
  rw [show n * n + 0 + 2 * n = n * n + 2 * n from by ring,
      show (2 : ℕ) + n + n = 2 * n + 2 from by ring,
      show (0 : ℕ) + n = n from by ring]
  -- State: (2, 0, 0, n, n²+2n, 2n+2)
  -- Phase 6: R2, R2 to finish
  step fm
  step fm
  rw [show n + 1 + 1 = n + 2 from by ring,
      show n * n + 2 * n + 1 + 1 = n * n + 2 * n + 2 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 1, n * n + 1, 2 * n⟩) 0
  intro n
  exists n + 1
  show ⟨(0 : ℕ), (0 : ℕ), 0, n + 1, n * n + 1, 2 * n⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), 0, n + 2, (n + 1) * (n + 1) + 1, 2 * (n + 1)⟩
  have h := main_transition n
  rw [show n * n + 2 * n + 2 = (n + 1) * (n + 1) + 1 from by ring,
      show 2 * n + 2 = 2 * (n + 1) from by ring] at h
  exact h

end Sz22_2003_unofficial_1251
