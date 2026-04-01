import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1554: [7/30, 9/2, 16/35, 5/3, 7/5]

Vector representation:
```
-1 -1 -1  1
-1  2  0  0
 4  0 -1 -1
 0 -1  1  0
 0  0 -1  1
```

This Fractran program halts.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1554

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+4, b, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

-- R4 chain: (0, b+k, c, 0) ⊢* (0, b, c+k, 0)
private theorem r4_chain : ∀ k, ∀ b c,
    ⟨(0 : ℕ), b + k, c, 0⟩ [fm]⊢* ⟨0, b, c + k, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    step fm; exact ih b (c + 1)

-- Loop step: (0, b+1, 0, d+1) -> R4 -> R3 -> R2x4 -> (0, b+8, 0, d)
private theorem loop_step : ∀ b d,
    ⟨(0 : ℕ), b + 1, 0, d + 1⟩ [fm]⊢* ⟨0, b + 8, (0 : ℕ), d⟩ := by
  intro b d
  step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Loop multi: iterate the loop k times
private theorem loop_multi : ∀ k, ∀ b d,
    ⟨(0 : ℕ), b + 1, 0, d + k⟩ [fm]⊢* ⟨0, b + 1 + 7 * k, (0 : ℕ), d⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show b + 1 + 7 * (k + 1) = (b + 7) + 1 + 7 * k from by ring,
        show b + 1 = (b + 0) + 1 from by ring]
    apply stepStar_trans (loop_step (b + 0) (d + k))
    rw [show b + 0 + 8 = (b + 7) + 1 from by ring]
    exact ih (b + 7) d

-- Opening: (4, 0, C+11, D) ⊢* (4, 0, C, D+5) in 15 steps
private theorem opening_11 : ∀ C D,
    ⟨(4 : ℕ), 0, C + 11, D⟩ [fm]⊢* ⟨4, 0, C, D + 5⟩ := by
  intro C D
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Opening multi: (4, 0, C + 11*q, D) ⊢* (4, 0, C, D + 5*q)
private theorem opening_multi : ∀ q, ∀ C D,
    ⟨(4 : ℕ), 0, C + 11 * q, D⟩ [fm]⊢* ⟨4, 0, C, D + 5 * q⟩ := by
  intro q; induction' q with q ih <;> intro C D
  · ring_nf; finish
  · rw [show C + 11 * (q + 1) = (C + 11) + 11 * q from by ring,
        show D + 5 * (q + 1) = D + 5 * q + 5 from by ring]
    apply stepStar_trans (ih (C + 11) D)
    exact opening_11 C (D + 5 * q)

-- Opening for r=0: (4, 0, 0, D) -> R2x4 -> (0, 8, 0, D)
private theorem opening_r0 : ∀ D,
    ⟨(4 : ℕ), 0, 0, D⟩ [fm]⊢* ⟨0, 8, (0 : ℕ), D⟩ := by
  intro D; step fm; step fm; step fm; step fm; ring_nf; finish

-- Opening for r=1: (4, 0, 1, D) -> (0, 5, 0, D+1)
private theorem opening_r1 : ∀ D,
    ⟨(4 : ℕ), 0, 1, D⟩ [fm]⊢* ⟨0, 5, (0 : ℕ), D + 1⟩ := by
  intro D; step fm; step fm; step fm; step fm; ring_nf; finish

-- Opening for r=2: (4, 0, 2, D) -> (0, 2, 0, D+2)
private theorem opening_r2 : ∀ D,
    ⟨(4 : ℕ), 0, 2, D⟩ [fm]⊢* ⟨0, 2, (0 : ℕ), D + 2⟩ := by
  intro D; step fm; step fm; step fm; step fm; ring_nf; finish

-- Opening for r=3: (4, 0, 3, D) -> (0, 10, 0, D+1)
private theorem opening_r3 : ∀ D,
    ⟨(4 : ℕ), 0, 3, D⟩ [fm]⊢* ⟨0, 10, (0 : ℕ), D + 1⟩ := by
  intro D
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Opening for r=4: (4, 0, 4, D) -> (0, 7, 0, D+2)
private theorem opening_r4 : ∀ D,
    ⟨(4 : ℕ), 0, 4, D⟩ [fm]⊢* ⟨0, 7, (0 : ℕ), D + 2⟩ := by
  intro D
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Opening for r=5: (4, 0, 5, D) -> (0, 4, 0, D+3)
private theorem opening_r5 : ∀ D,
    ⟨(4 : ℕ), 0, 5, D⟩ [fm]⊢* ⟨0, 4, (0 : ℕ), D + 3⟩ := by
  intro D
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Opening for r=6: (4, 0, 6, D) -> (0, 1, 0, D+4)
private theorem opening_r6 : ∀ D,
    ⟨(4 : ℕ), 0, 6, D⟩ [fm]⊢* ⟨0, 1, (0 : ℕ), D + 4⟩ := by
  intro D
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Opening for r=7: (4, 0, 7, D) -> (0, 9, 0, D+3)
private theorem opening_r7 : ∀ D,
    ⟨(4 : ℕ), 0, 7, D⟩ [fm]⊢* ⟨0, 9, (0 : ℕ), D + 3⟩ := by
  intro D
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Opening for r=8: (4, 0, 8, D) -> (0, 6, 0, D+4)
private theorem opening_r8 : ∀ D,
    ⟨(4 : ℕ), 0, 8, D⟩ [fm]⊢* ⟨0, 6, (0 : ℕ), D + 4⟩ := by
  intro D
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Opening for r=9: (4, 0, 9, D) -> (0, 3, 0, D+5)
private theorem opening_r9 : ∀ D,
    ⟨(4 : ℕ), 0, 9, D⟩ [fm]⊢* ⟨0, 3, (0 : ℕ), D + 5⟩ := by
  intro D
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Opening for r=10 (halting): (4, 0, 10, D) -> (0, 0, 0, D+6)
private theorem opening_r10 : ∀ D,
    ⟨(4 : ℕ), 0, 10, D⟩ [fm]⊢* ⟨0, 0, 0, D + 6⟩ := by
  intro D
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  ring_nf; finish

private theorem halted_at : ∀ d, halted fm ⟨(0 : ℕ), 0, 0, d⟩ := by
  intro d; rfl

-- Helper: combine opening_multi + opening_rX + loop + r4_chain
-- Pattern: (0, 0, 11*q + r + 2, 0) -> R5 -> R3 -> (4, 0, r + 11*q, 0)
--   -> opening_multi -> (4, 0, r, 5*q) -> opening_rX -> (0, B, 0, 5*q + d_r)
--   -> loop -> (0, B + 7*(5*q + d_r), 0, 0) -> r4_chain -> (0, 0, total, 0)

-- cycle_r0: (0, 0, 11*q + 2, 0) ⊢* (0, 0, 35*q + 8, 0)
-- B=8, d_r=0. total = 8 + 7*5q = 8 + 35q
private theorem cycle_r0 (q : ℕ) :
    ⟨(0 : ℕ), 0, 11 * q + 2, 0⟩ [fm]⊢* ⟨0, 0, 35 * q + 8, (0 : ℕ)⟩ := by
  rw [show 11 * q + 2 = (0 + 11 * q + 1) + 1 from by ring]
  step fm
  rw [show (0 + 11 * q + 1 : ℕ) = (0 + 11 * q) + 1 from by ring]
  step fm
  rw [show (0 + 11 * q : ℕ) = 0 + 11 * q from by ring]
  apply stepStar_trans (opening_multi q 0 0)
  rw [show 0 + 5 * q = 5 * q from by ring]
  apply stepStar_trans (opening_r0 (5 * q))
  rw [show (8 : ℕ) = 7 + 1 from by ring,
      show 5 * q = 0 + 5 * q from by ring]
  apply stepStar_trans (loop_multi (5 * q) 7 0)
  rw [show 7 + 1 + 7 * (5 * q) = 0 + (35 * q + 8) from by ring]
  apply stepStar_trans (r4_chain (35 * q + 8) 0 0)
  ring_nf; finish

-- cycle_r1: (0, 0, 11*q + 3, 0) ⊢* (0, 0, 35*q + 12, 0)
-- B=5, d_r=1. total = 5 + 7*(5q+1) = 5 + 35q + 7 = 35q + 12
private theorem cycle_r1 (q : ℕ) :
    ⟨(0 : ℕ), 0, 11 * q + 3, 0⟩ [fm]⊢* ⟨0, 0, 35 * q + 12, (0 : ℕ)⟩ := by
  rw [show 11 * q + 3 = (1 + 11 * q + 1) + 1 from by ring]
  step fm
  rw [show (1 + 11 * q + 1 : ℕ) = (1 + 11 * q) + 1 from by ring]
  step fm
  apply stepStar_trans (opening_multi q 1 0)
  rw [show 0 + 5 * q = 5 * q from by ring]
  apply stepStar_trans (opening_r1 (5 * q))
  rw [show 5 * q + 1 = 0 + (5 * q + 1) from by ring,
      show (5 : ℕ) = 4 + 1 from by ring]
  apply stepStar_trans (loop_multi (5 * q + 1) 4 0)
  rw [show 4 + 1 + 7 * (5 * q + 1) = 0 + (35 * q + 12) from by ring]
  apply stepStar_trans (r4_chain (35 * q + 12) 0 0)
  ring_nf; finish

-- cycle_r2: (0, 0, 11*q + 4, 0) ⊢* (0, 0, 35*q + 16, 0)
-- B=2, d_r=2. total = 2 + 7*(5q+2) = 2 + 35q + 14 = 35q + 16
private theorem cycle_r2 (q : ℕ) :
    ⟨(0 : ℕ), 0, 11 * q + 4, 0⟩ [fm]⊢* ⟨0, 0, 35 * q + 16, (0 : ℕ)⟩ := by
  rw [show 11 * q + 4 = (2 + 11 * q + 1) + 1 from by ring]
  step fm
  rw [show (2 + 11 * q + 1 : ℕ) = (2 + 11 * q) + 1 from by ring]
  step fm
  apply stepStar_trans (opening_multi q 2 0)
  rw [show 0 + 5 * q = 5 * q from by ring]
  apply stepStar_trans (opening_r2 (5 * q))
  rw [show 5 * q + 2 = 0 + (5 * q + 2) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (loop_multi (5 * q + 2) 1 0)
  rw [show 1 + 1 + 7 * (5 * q + 2) = 0 + (35 * q + 16) from by ring]
  apply stepStar_trans (r4_chain (35 * q + 16) 0 0)
  ring_nf; finish

-- cycle_r3: (0, 0, 11*q + 5, 0) ⊢* (0, 0, 35*q + 17, 0)
-- B=10, d_r=1. total = 10 + 7*(5q+1) = 10 + 35q + 7 = 35q + 17
private theorem cycle_r3 (q : ℕ) :
    ⟨(0 : ℕ), 0, 11 * q + 5, 0⟩ [fm]⊢* ⟨0, 0, 35 * q + 17, (0 : ℕ)⟩ := by
  rw [show 11 * q + 5 = (3 + 11 * q + 1) + 1 from by ring]
  step fm
  rw [show (3 + 11 * q + 1 : ℕ) = (3 + 11 * q) + 1 from by ring]
  step fm
  apply stepStar_trans (opening_multi q 3 0)
  rw [show 0 + 5 * q = 5 * q from by ring]
  apply stepStar_trans (opening_r3 (5 * q))
  rw [show 5 * q + 1 = 0 + (5 * q + 1) from by ring,
      show (10 : ℕ) = 9 + 1 from by ring]
  apply stepStar_trans (loop_multi (5 * q + 1) 9 0)
  rw [show 9 + 1 + 7 * (5 * q + 1) = 0 + (35 * q + 17) from by ring]
  apply stepStar_trans (r4_chain (35 * q + 17) 0 0)
  ring_nf; finish

-- cycle_r4: (0, 0, 11*q + 6, 0) ⊢* (0, 0, 35*q + 21, 0)
-- B=7, d_r=2. total = 7 + 7*(5q+2) = 7 + 35q + 14 = 35q + 21
private theorem cycle_r4 (q : ℕ) :
    ⟨(0 : ℕ), 0, 11 * q + 6, 0⟩ [fm]⊢* ⟨0, 0, 35 * q + 21, (0 : ℕ)⟩ := by
  rw [show 11 * q + 6 = (4 + 11 * q + 1) + 1 from by ring]
  step fm
  rw [show (4 + 11 * q + 1 : ℕ) = (4 + 11 * q) + 1 from by ring]
  step fm
  apply stepStar_trans (opening_multi q 4 0)
  rw [show 0 + 5 * q = 5 * q from by ring]
  apply stepStar_trans (opening_r4 (5 * q))
  rw [show 5 * q + 2 = 0 + (5 * q + 2) from by ring,
      show (7 : ℕ) = 6 + 1 from by ring]
  apply stepStar_trans (loop_multi (5 * q + 2) 6 0)
  rw [show 6 + 1 + 7 * (5 * q + 2) = 0 + (35 * q + 21) from by ring]
  apply stepStar_trans (r4_chain (35 * q + 21) 0 0)
  ring_nf; finish

-- cycle_r5: (0, 0, 11*q + 7, 0) ⊢* (0, 0, 35*q + 25, 0)
-- B=4, d_r=3. total = 4 + 7*(5q+3) = 4 + 35q + 21 = 35q + 25
private theorem cycle_r5 (q : ℕ) :
    ⟨(0 : ℕ), 0, 11 * q + 7, 0⟩ [fm]⊢* ⟨0, 0, 35 * q + 25, (0 : ℕ)⟩ := by
  rw [show 11 * q + 7 = (5 + 11 * q + 1) + 1 from by ring]
  step fm
  rw [show (5 + 11 * q + 1 : ℕ) = (5 + 11 * q) + 1 from by ring]
  step fm
  apply stepStar_trans (opening_multi q 5 0)
  rw [show 0 + 5 * q = 5 * q from by ring]
  apply stepStar_trans (opening_r5 (5 * q))
  rw [show 5 * q + 3 = 0 + (5 * q + 3) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (loop_multi (5 * q + 3) 3 0)
  rw [show 3 + 1 + 7 * (5 * q + 3) = 0 + (35 * q + 25) from by ring]
  apply stepStar_trans (r4_chain (35 * q + 25) 0 0)
  ring_nf; finish

-- cycle_r6: (0, 0, 11*q + 8, 0) ⊢* (0, 0, 35*q + 29, 0)
-- B=1, d_r=4. total = 1 + 7*(5q+4) = 1 + 35q + 28 = 35q + 29
private theorem cycle_r6 (q : ℕ) :
    ⟨(0 : ℕ), 0, 11 * q + 8, 0⟩ [fm]⊢* ⟨0, 0, 35 * q + 29, (0 : ℕ)⟩ := by
  rw [show 11 * q + 8 = (6 + 11 * q + 1) + 1 from by ring]
  step fm
  rw [show (6 + 11 * q + 1 : ℕ) = (6 + 11 * q) + 1 from by ring]
  step fm
  apply stepStar_trans (opening_multi q 6 0)
  rw [show 0 + 5 * q = 5 * q from by ring]
  apply stepStar_trans (opening_r6 (5 * q))
  rw [show 5 * q + 4 = 0 + (5 * q + 4) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (loop_multi (5 * q + 4) 0 0)
  rw [show 0 + 1 + 7 * (5 * q + 4) = 0 + (35 * q + 29) from by ring]
  apply stepStar_trans (r4_chain (35 * q + 29) 0 0)
  ring_nf; finish

-- cycle_r7: (0, 0, 11*q + 9, 0) ⊢* (0, 0, 35*q + 30, 0)
-- B=9, d_r=3. total = 9 + 7*(5q+3) = 9 + 35q + 21 = 35q + 30
private theorem cycle_r7 (q : ℕ) :
    ⟨(0 : ℕ), 0, 11 * q + 9, 0⟩ [fm]⊢* ⟨0, 0, 35 * q + 30, (0 : ℕ)⟩ := by
  rw [show 11 * q + 9 = (7 + 11 * q + 1) + 1 from by ring]
  step fm
  rw [show (7 + 11 * q + 1 : ℕ) = (7 + 11 * q) + 1 from by ring]
  step fm
  apply stepStar_trans (opening_multi q 7 0)
  rw [show 0 + 5 * q = 5 * q from by ring]
  apply stepStar_trans (opening_r7 (5 * q))
  rw [show 5 * q + 3 = 0 + (5 * q + 3) from by ring,
      show (9 : ℕ) = 8 + 1 from by ring]
  apply stepStar_trans (loop_multi (5 * q + 3) 8 0)
  rw [show 8 + 1 + 7 * (5 * q + 3) = 0 + (35 * q + 30) from by ring]
  apply stepStar_trans (r4_chain (35 * q + 30) 0 0)
  ring_nf; finish

-- cycle_r8: (0, 0, 11*q + 10, 0) ⊢* (0, 0, 35*q + 34, 0)
-- B=6, d_r=4. total = 6 + 7*(5q+4) = 6 + 35q + 28 = 35q + 34
private theorem cycle_r8 (q : ℕ) :
    ⟨(0 : ℕ), 0, 11 * q + 10, 0⟩ [fm]⊢* ⟨0, 0, 35 * q + 34, (0 : ℕ)⟩ := by
  rw [show 11 * q + 10 = (8 + 11 * q + 1) + 1 from by ring]
  step fm
  rw [show (8 + 11 * q + 1 : ℕ) = (8 + 11 * q) + 1 from by ring]
  step fm
  apply stepStar_trans (opening_multi q 8 0)
  rw [show 0 + 5 * q = 5 * q from by ring]
  apply stepStar_trans (opening_r8 (5 * q))
  rw [show 5 * q + 4 = 0 + (5 * q + 4) from by ring,
      show (6 : ℕ) = 5 + 1 from by ring]
  apply stepStar_trans (loop_multi (5 * q + 4) 5 0)
  rw [show 5 + 1 + 7 * (5 * q + 4) = 0 + (35 * q + 34) from by ring]
  apply stepStar_trans (r4_chain (35 * q + 34) 0 0)
  ring_nf; finish

-- cycle_r9: (0, 0, 11*q + 11, 0) ⊢* (0, 0, 35*q + 38, 0)
-- B=3, d_r=5. total = 3 + 7*(5q+5) = 3 + 35q + 35 = 35q + 38
private theorem cycle_r9 (q : ℕ) :
    ⟨(0 : ℕ), 0, 11 * q + 11, 0⟩ [fm]⊢* ⟨0, 0, 35 * q + 38, (0 : ℕ)⟩ := by
  rw [show 11 * q + 11 = (9 + 11 * q + 1) + 1 from by ring]
  step fm
  rw [show (9 + 11 * q + 1 : ℕ) = (9 + 11 * q) + 1 from by ring]
  step fm
  apply stepStar_trans (opening_multi q 9 0)
  rw [show 0 + 5 * q = 5 * q from by ring]
  apply stepStar_trans (opening_r9 (5 * q))
  rw [show 5 * q + 5 = 0 + (5 * q + 5) from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (loop_multi (5 * q + 5) 2 0)
  rw [show 2 + 1 + 7 * (5 * q + 5) = 0 + (35 * q + 38) from by ring]
  apply stepStar_trans (r4_chain (35 * q + 38) 0 0)
  ring_nf; finish

-- cycle_to_halt: (0, 0, 11*q + 12, 0) ⊢* (0, 0, 0, 5*q + 6)
private theorem cycle_to_halt (q : ℕ) :
    ⟨(0 : ℕ), 0, 11 * q + 12, 0⟩ [fm]⊢* ⟨0, 0, 0, 5 * q + 6⟩ := by
  rw [show 11 * q + 12 = (10 + 11 * q + 1) + 1 from by ring]
  step fm
  rw [show (10 + 11 * q + 1 : ℕ) = (10 + 11 * q) + 1 from by ring]
  step fm
  apply stepStar_trans (opening_multi q 10 0)
  rw [show 0 + 5 * q = 5 * q from by ring]
  apply stepStar_trans (opening_r10 (5 * q))
  ring_nf; finish

theorem halts_thm : halts fm c₀ := by
  apply stepStar_halts (c₂ := ⟨0, 0, 2, 0⟩) (by execute fm 3)
  apply stepStar_halts (c₂ := ⟨0, 0, 8, 0⟩)
  · rw [show (2 : ℕ) = 11 * 0 + 2 from by ring,
        show (8 : ℕ) = 35 * 0 + 8 from by ring]
    exact cycle_r0 0
  apply stepStar_halts (c₂ := ⟨0, 0, 29, 0⟩)
  · rw [show (8 : ℕ) = 11 * 0 + 8 from by ring,
        show (29 : ℕ) = 35 * 0 + 29 from by ring]
    exact cycle_r6 0
  apply stepStar_halts (c₂ := ⟨0, 0, 95, 0⟩)
  · rw [show (29 : ℕ) = 11 * 2 + 7 from by ring,
        show (95 : ℕ) = 35 * 2 + 25 from by ring]
    exact cycle_r5 2
  apply stepStar_halts (c₂ := ⟨0, 0, 305, 0⟩)
  · rw [show (95 : ℕ) = 11 * 8 + 7 from by ring,
        show (305 : ℕ) = 35 * 8 + 25 from by ring]
    exact cycle_r5 8
  apply stepStar_halts (c₂ := ⟨0, 0, 974, 0⟩)
  · rw [show (305 : ℕ) = 11 * 27 + 8 from by ring,
        show (974 : ℕ) = 35 * 27 + 29 from by ring]
    exact cycle_r6 27
  apply stepStar_halts (c₂ := ⟨0, 0, 3101, 0⟩)
  · rw [show (974 : ℕ) = 11 * 88 + 6 from by ring,
        show (3101 : ℕ) = 35 * 88 + 21 from by ring]
    exact cycle_r4 88
  apply stepStar_halts (c₂ := ⟨0, 0, 9869, 0⟩)
  · rw [show (3101 : ℕ) = 11 * 281 + 10 from by ring,
        show (9869 : ℕ) = 35 * 281 + 34 from by ring]
    exact cycle_r8 281
  apply stepStar_halts (c₂ := ⟨0, 0, 31403, 0⟩)
  · rw [show (9869 : ℕ) = 11 * 897 + 2 from by ring,
        show (31403 : ℕ) = 35 * 897 + 8 from by ring]
    exact cycle_r0 897
  apply stepStar_halts (c₂ := ⟨0, 0, 99920, 0⟩)
  · rw [show (31403 : ℕ) = 11 * 2854 + 9 from by ring,
        show (99920 : ℕ) = 35 * 2854 + 30 from by ring]
    exact cycle_r7 2854
  apply stepStar_halts (c₂ := ⟨0, 0, 317930, 0⟩)
  · rw [show (99920 : ℕ) = 11 * 9083 + 7 from by ring,
        show (317930 : ℕ) = 35 * 9083 + 25 from by ring]
    exact cycle_r5 9083
  apply stepStar_halts (c₂ := ⟨0, 0, 1011599, 0⟩)
  · rw [show (317930 : ℕ) = 11 * 28902 + 8 from by ring,
        show (1011599 : ℕ) = 35 * 28902 + 29 from by ring]
    exact cycle_r6 28902
  apply stepStar_halts (c₂ := ⟨0, 0, 3218726, 0⟩)
  · rw [show (1011599 : ℕ) = 11 * 91963 + 6 from by ring,
        show (3218726 : ℕ) = 35 * 91963 + 21 from by ring]
    exact cycle_r4 91963
  apply stepStar_halts (c₂ := ⟨0, 0, 10241402, 0⟩)
  · rw [show (3218726 : ℕ) = 11 * 292611 + 5 from by ring,
        show (10241402 : ℕ) = 35 * 292611 + 17 from by ring]
    exact cycle_r3 292611
  apply stepStar_halts (c₂ := ⟨0, 0, 32586281, 0⟩)
  · rw [show (10241402 : ℕ) = 11 * 931036 + 6 from by ring,
        show (32586281 : ℕ) = 35 * 931036 + 21 from by ring]
    exact cycle_r4 931036
  apply stepStar_halts (c₂ := ⟨0, 0, 103683623, 0⟩)
  · rw [show (32586281 : ℕ) = 11 * 2962389 + 2 from by ring,
        show (103683623 : ℕ) = 35 * 2962389 + 8 from by ring]
    exact cycle_r0 2962389
  apply stepStar_halts (c₂ := ⟨0, 0, 329902439, 0⟩)
  · rw [show (103683623 : ℕ) = 11 * 9425783 + 10 from by ring,
        show (329902439 : ℕ) = 35 * 9425783 + 34 from by ring]
    exact cycle_r8 9425783
  apply stepStar_halts (c₂ := ⟨0, 0, 1049689580, 0⟩)
  · rw [show (329902439 : ℕ) = 11 * 29991130 + 9 from by ring,
        show (1049689580 : ℕ) = 35 * 29991130 + 30 from by ring]
    exact cycle_r7 29991130
  apply stepStar_halts (c₂ := ⟨0, 0, 3339921392, 0⟩)
  · rw [show (1049689580 : ℕ) = 11 * 95426325 + 5 from by ring,
        show (3339921392 : ℕ) = 35 * 95426325 + 17 from by ring]
    exact cycle_r3 95426325
  apply stepStar_halts (c₂ := ⟨0, 0, 10627022612, 0⟩)
  · rw [show (3339921392 : ℕ) = 11 * 303629217 + 5 from by ring,
        show (10627022612 : ℕ) = 35 * 303629217 + 17 from by ring]
    exact cycle_r3 303629217
  apply stepStar_halts (c₂ := ⟨0, 0, 33813253769, 0⟩)
  · rw [show (10627022612 : ℕ) = 11 * 966092964 + 8 from by ring,
        show (33813253769 : ℕ) = 35 * 966092964 + 29 from by ring]
    exact cycle_r6 966092964
  apply stepStar_halts (c₂ := ⟨0, 0, 107587625630, 0⟩)
  · rw [show (33813253769 : ℕ) = 11 * 3073932160 + 9 from by ring,
        show (107587625630 : ℕ) = 35 * 3073932160 + 30 from by ring]
    exact cycle_r7 3073932160
  apply stepStar_halts (c₂ := ⟨0, 0, 0, 48903466196⟩)
  · rw [show (107587625630 : ℕ) = 11 * 9780693238 + 12 from by ring,
        show (48903466196 : ℕ) = 5 * 9780693238 + 6 from by ring]
    exact cycle_to_halt 9780693238
  exact halted_halts (halted_at 48903466196)

end Sz22_2003_unofficial_1554
