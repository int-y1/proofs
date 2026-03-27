import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #359: [2/15, 3/14, 1375/2, 7/25, 6/11]

Vector representation:
```
 1 -1 -1  0  0
-1  1  0 -1  0
-1  0  3  0  1
 0  0 -2  1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_359

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e+1⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R3 drain: apply rule 3 repeatedly to convert a to c and e
theorem r3_drain : ∀ j, ∀ c e,
    ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 3 * j, 0, e + j⟩ := by
  intro j; induction j with
  | zero => intro c e; exists 0
  | succ j ih =>
    intro c e
    show ⟨(j) + 1, 0, c, 0, e⟩ [fm]⊢* _
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R4 loop: convert c pairs to d
theorem r4_loop : ∀ j, ∀ c d e,
    ⟨0, 0, c + 2 * j, d, e⟩ [fm]⊢* ⟨0, 0, c, d + j, e⟩ := by
  intro j; induction j with
  | zero => intro c d e; exists 0
  | succ j ih =>
    intro c d e
    rw [show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R5/R2 pair: one iteration of the descent loop
theorem r5r2_pair : ∀ b d e,
    ⟨0, b, 0, d + 1, e + 1⟩ [fm]⊢* ⟨0, b + 2, 0, d, e⟩ := by
  intro b d e; step fm; step fm; finish

-- R5/R2 loop: iterate the descent
theorem r5r2_loop : ∀ j, ∀ b d e,
    ⟨0, b, 0, d + j, e + j⟩ [fm]⊢* ⟨0, b + 2 * j, 0, d, e⟩ := by
  intro j; induction j with
  | zero => intro b d e; exists 0
  | succ j ih =>
    intro b d e
    rw [show d + (j + 1) = (d + j) + 1 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    apply stepStar_trans (r5r2_pair _ _ _)
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Climbing phase: generalized
-- (a+1, b, 0, 0, e) ->* (0, 0, 3*(a+1)+2*b, 0, e+a+1+b)
theorem climb_gen : ∀ b, ∀ a e,
    ⟨a + 1, b, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 3 * a + 3 + 2 * b, 0, e + a + 1 + b⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a e
  rcases b with _ | _ | _ | b
  · -- b = 0
    show ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢* _
    apply stepStar_trans (r3_drain (a + 1) 0 e)
    ring_nf; finish
  · -- b = 1
    show ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢* _
    step fm -- R3: (a, 1, 3, 0, e+1)
    step fm -- R1: (a+1, 0, 2, 0, e+1)
    apply stepStar_trans (r3_drain (a + 1) 2 (e + 1))
    ring_nf; finish
  · -- b = 2
    show ⟨a + 1, 2, 0, 0, e⟩ [fm]⊢* _
    step fm -- R3: (a, 2, 3, 0, e+1)
    step fm -- R1: (a+1, 1, 2, 0, e+1)
    step fm -- R1: (a+2, 0, 1, 0, e+1)
    apply stepStar_trans (r3_drain (a + 2) 1 (e + 1))
    ring_nf; finish
  · -- b = b + 3
    show ⟨a + 1, b + 3, 0, 0, e⟩ [fm]⊢* _
    step fm -- R3: (a, b+3, 3, 0, e+1)
    step fm -- R1: (a+1, b+2, 2, 0, e+1)
    step fm -- R1: (a+2, b+1, 1, 0, e+1)
    step fm -- R1: (a+3, b, 0, 0, e+1)
    have h := ih b (by omega) (a + 2) (e + 1)
    apply stepStar_trans h
    ring_nf; finish

-- Descent: (0, 0, 1, n+1, n+1) ->* (1, 2*n+1, 0, 0, 0)
-- Entry: R5, R1, R2, R2, then r5r2_loop, then final R5
theorem descent : ∀ n,
    ⟨0, 0, 1, n + 1, n + 1⟩ [fm]⊢* ⟨1, 2 * n + 1, 0, 0, 0⟩ := by
  intro n; rcases n with _ | n
  · -- n = 0: (0, 0, 1, 1, 1) ->* (1, 1, 0, 0, 0)
    step fm; step fm; step fm; finish
  · -- n >= 1: (0, 0, 1, n+2, n+2)
    step fm; step fm; step fm; step fm
    -- Goal: (0, 2, 0, n, n + 1) ⊢* (1, 2*(n+1)+1, 0, 0, 0)
    have h := r5r2_loop n 2 0 1
    simp only [Nat.zero_add, Nat.add_comm 1 n] at h
    apply stepStar_trans h
    -- Goal: (0, 2 + 2*n, 0, 0, 1) ⊢* (1, 2*(n+1)+1, 0, 0, 0)
    -- Apply rule 5: e+1 -> a+1, b+1
    rw [show 2 + 2 * n = (1 + 2 * n) + 1 from by ring]
    step fm
    ring_nf; finish

-- Main transition: one full cycle
-- C(b) = (0, 0, 2*b+3, 0, b+1) ⊢⁺ C(2*b+1) = (0, 0, 4*b+5, 0, 2*b+2)
theorem main_trans (b : ℕ) :
    ⟨0, 0, 2 * b + 3, 0, b + 1⟩ [fm]⊢⁺ ⟨0, 0, 4 * b + 5, 0, 2 * b + 2⟩ := by
  -- Phase 1: R4 (first step gives ⊢⁺)
  rw [show 2 * b + 3 = 1 + 2 * (b + 1) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 1 + 2 * (b + 1), 0, b + 1⟩ = _
    rw [show 1 + 2 * (b + 1) = (1 + 2 * b) + 2 from by ring]; rfl
  -- Remaining R4 steps
  apply stepStar_trans (r4_loop b 1 1 (b + 1))
  -- Phase 2: Descent
  rw [show (1 : ℕ) + b = b + 1 from by ring]
  apply stepStar_trans (descent b)
  -- Phase 3: Climbing
  have h := climb_gen (2 * b + 1) 0 0
  rw [show (0 : ℕ) + 1 = 1 from by ring,
      show 3 * 0 + 3 + 2 * (2 * b + 1) = 4 * b + 5 from by ring,
      show 0 + 0 + 1 + (2 * b + 1) = 2 * b + 2 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun b ↦ ⟨0, 0, 2 * b + 3, 0, b + 1⟩) 0
  intro b
  refine ⟨2 * b + 1, ?_⟩
  rw [show 2 * (2 * b + 1) + 3 = 4 * b + 5 from by ring,
      show 2 * b + 1 + 1 = 2 * b + 2 from by ring]
  exact main_trans b

end Sz22_2003_unofficial_359
