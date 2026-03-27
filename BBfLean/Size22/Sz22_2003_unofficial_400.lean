import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #400: [20/3, 9/35, 1/20, 49/2, 3/7]

Vector representation:
```
 2 -1  1  0
 0  2 -1 -1
-2  0 -1  0
-1  0  0  2
 0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_400

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a, b, c+1, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+2, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- Phase 1: drain a to d when b=0, c=0
-- Rule 4: (a+1, 0, 0, d) -> (a, 0, 0, d+2)
theorem a_to_d : ∀ k a d, ⟨a+k, 0, 0, d⟩ [fm]⊢* ⟨a, 0, 0, d+2*k⟩ := by
  intro k; induction k with
  | zero => intro a d; exists 0
  | succ k ih =>
    intro a d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2))
    ring_nf; finish

-- Phase 2: start the build from (0, 0, 0, d+1)
-- Rule 5: (0, 0, 0, d+1) -> (0, 1, 0, d)
-- Rule 1: (0, 1, 0, d) -> (2, 0, 1, d)
theorem start_build (d : ℕ) : ⟨0, 0, 0, d+1⟩ [fm]⊢⁺ ⟨2, 0, 1, d⟩ := by
  execute fm 2

-- Phase 3: build loop. Each iteration does R2,R1,R1 consuming one d.
-- From (2+4*k, 0, 1+k, j) after j iterations: (2+4*(k+j), 0, 1+k+j, 0)
theorem build_loop : ∀ j k, ⟨2+4*k, 0, k+1, j⟩ [fm]⊢* ⟨2+4*(k+j), 0, k+j+1, 0⟩ := by
  intro j; induction j with
  | zero => intro k; ring_nf; exists 0
  | succ j ih =>
    intro k
    step fm; step fm; step fm
    show ⟨2+4*k+4, 0, k+1+1, j⟩ [fm]⊢* ⟨2+4*(k+(j+1)), 0, k+(j+1)+1, 0⟩
    rw [show 2+4*k+4 = 2+4*(k+1) from by ring,
        show k+1+1 = (k+1)+1 from by ring]
    apply stepStar_trans (ih (k+1))
    ring_nf; finish

-- Phase 4: drain a and c when b=0, d=0
-- Rule 3: (a+2, 0, c+1, 0) -> (a, 0, c, 0)
theorem drain_ac : ∀ k a, ⟨a+2*k, 0, k, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a; exists 0
  | succ k ih =>
    intro a
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring]
    step fm
    exact ih a

-- Main cycle: (2*(n+1), 0, 0, 0) ⊢⁺ (8*n+6, 0, 0, 0) for all n
-- From (2*(n+1), 0, 0, 0) = (2n+2, 0, 0, 0):
--   Phase 1: -> (0, 0, 0, 2*(2n+2)) = (0, 0, 0, 4n+4) = (0, 0, 0, (4n+3)+1)
--   Phase 2: -> (2, 0, 1, 4n+3)
--   Phase 3: k=0, j=4n+3 -> (2+4*(4n+3), 0, 1+(4n+3), 0) = (16n+14, 0, 4n+4, 0)
--   Phase 4: k=4n+4, a = 16n+14 - 2*(4n+4) = 8n+6 -> (8n+6, 0, 0, 0)
theorem cycle (n : ℕ) : ⟨2*(n+1), 0, 0, 0⟩ [fm]⊢⁺ ⟨8*n+6, 0, 0, 0⟩ := by
  -- Phase 1: drain a to d
  apply stepStar_stepPlus_stepPlus
  · have h := a_to_d (2*(n+1)) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: start build
  apply stepPlus_stepStar_stepPlus
  · rw [show 2 * (2 * (n + 1)) = (4*n+3)+1 from by ring]
    exact start_build (4*n+3)
  -- Phase 3: build loop
  apply stepStar_trans
  · have h := build_loop (4*n+3) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 4: drain a and c
  show ⟨2+4*(4*n+3), 0, (4*n+3)+1, 0⟩ [fm]⊢* ⟨8*n+6, 0, 0, 0⟩
  have h := drain_ac ((4*n+3)+1) (8*n+6)
  rw [show 8*n+6 + 2*((4*n+3)+1) = 2+4*(4*n+3) from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨2, 0, 0, 0⟩ : Q))
  · execute fm 8
  exact progress_nonhalt_simple (fm := fm) (fun n ↦ (⟨2*(n+1), 0, 0, 0⟩ : Q)) 0
    (fun n ↦ ⟨4*n+2, by
      have h := cycle n
      show (⟨2*(n+1), 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨2*(4*n+2+1), 0, 0, 0⟩
      rw [show 2*(4*n+2+1) = 8*n+6 from by ring]
      exact h⟩)

end Sz22_2003_unofficial_400
