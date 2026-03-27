import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #360: [2/15, 3/14, 15125/2, 7/5, 10/11]

Vector representation:
```
 1 -1 -1  0  0
-1  1  0 -1  0
-1  0  3  0  2
 0  0 -1  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_360

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R3 drain: apply rule 3 repeatedly to convert a to c and e
theorem r3_drain : ∀ j, ∀ c e,
    ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 3 * j, 0, e + 2 * j⟩ := by
  intro j; induction j with
  | zero => intro c e; exists 0
  | succ j ih =>
    intro c e
    show ⟨(j) + 1, 0, c, 0, e⟩ [fm]⊢* _
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R4 loop: transfer c to d
theorem r4_loop : ∀ j, ∀ c d e,
    ⟨0, 0, c + j, d, e⟩ [fm]⊢* ⟨0, 0, c, d + j, e⟩ := by
  intro j; induction j with
  | zero => intro c d e; exists 0
  | succ j ih =>
    intro c d e
    rw [show c + (j + 1) = (c + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Middle loop init: (0, 0, 0, d+2, e+1) -> (0, 1, 0, d, e) via R5, R2, R1, R2
theorem middle_init : ∀ d e,
    ⟨0, 0, 0, d + 2, e + 1⟩ [fm]⊢* ⟨0, 1, 0, d, e⟩ := by
  intro d e; step fm; step fm; step fm; step fm; finish

-- Middle loop iteration: (0, j+1, 0, d+2, e+1) -> (0, j+2, 0, d, e) via R5, R1, R2, R2
theorem middle_iter : ∀ j d e,
    ⟨0, j + 1, 0, d + 2, e + 1⟩ [fm]⊢* ⟨0, j + 2, 0, d, e⟩ := by
  intro j d e; step fm; step fm; step fm; step fm; ring_nf; finish

-- Middle loop: iterate from j=1 to k
theorem middle_loop : ∀ k, ∀ j d e,
    ⟨0, j + 1, 0, d + 2 * k, e + k⟩ [fm]⊢* ⟨0, j + 1 + k, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro j d e; exists 0
  | succ k ih =>
    intro j d e
    rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans (middle_iter _ _ _)
    apply stepStar_trans (ih (j + 1) _ _)
    ring_nf; finish

-- Tail step: (0, n+1, 0, 1, e+1) -> (1, n+1, 0, 0, e) via R5, R1, R2
theorem tail_step : ∀ n e,
    ⟨0, n + 1, 0, 1, e + 1⟩ [fm]⊢* ⟨1, n + 1, 0, 0, e⟩ := by
  intro n e; step fm; step fm; step fm; ring_nf; finish

-- Climbing phase: (a+1, b, 0, 0, e) ->* (0, 0, 3*(a+1)+2*b, 0, e+2*(a+1)+2*b)
theorem climb_gen : ∀ b, ∀ a e,
    ⟨a + 1, b, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 3 * a + 3 + 2 * b, 0, e + 2 * a + 2 + 2 * b⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a e
  rcases b with _ | _ | _ | b
  · -- b = 0
    show ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢* _
    apply stepStar_trans (r3_drain (a + 1) 0 e)
    ring_nf; finish
  · -- b = 1
    show ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢* _
    step fm -- R3: (a, 1, 3, 0, e+2)
    step fm -- R1: (a+1, 0, 2, 0, e+2)
    apply stepStar_trans (r3_drain (a + 1) 2 (e + 2))
    ring_nf; finish
  · -- b = 2
    show ⟨a + 1, 2, 0, 0, e⟩ [fm]⊢* _
    step fm -- R3: (a, 2, 3, 0, e+2)
    step fm -- R1: (a+1, 1, 2, 0, e+2)
    step fm -- R1: (a+2, 0, 1, 0, e+2)
    apply stepStar_trans (r3_drain (a + 2) 1 (e + 2))
    ring_nf; finish
  · -- b = b + 3
    show ⟨a + 1, b + 3, 0, 0, e⟩ [fm]⊢* _
    step fm -- R3: (a, b+3, 3, 0, e+2)
    step fm -- R1: (a+1, b+2, 2, 0, e+2)
    step fm -- R1: (a+2, b+1, 1, 0, e+2)
    step fm -- R1: (a+3, b, 0, 0, e+2)
    have h := ih b (by omega) (a + 2) (e + 2)
    apply stepStar_trans h
    ring_nf; finish

-- Define the recurrence for e values
def E : ℕ → ℕ
  | 0 => 2
  | n + 1 => E n + n + 2

-- E is always at least n + 2
theorem E_ge : ∀ n, E n ≥ n + 2 := by
  intro n; induction n with
  | zero => simp [E]
  | succ n ih => simp [E]; omega

-- Main transition: one full cycle
theorem main_trans (n : ℕ) :
    ⟨0, 0, 2 * n + 3, 0, E n⟩ [fm]⊢⁺ ⟨0, 0, 2 * (n + 1) + 3, 0, E (n + 1)⟩ := by
  have hE := E_ge n
  -- Phase 1: R4 chain (first step gives ⊢⁺, then remaining R4 steps)
  rw [show 2 * n + 3 = 0 + (2 * n + 3) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0 + (2 * n + 3), 0, E n⟩ = _
    rw [show 0 + (2 * n + 3) = (2 * n + 2) + 1 from by ring]; rfl
  -- After first R4 step: (0, 0, 2n+2, 1, E n)
  -- Need to show (0, 0, 2n+2, 1, E n) ⊢* target
  -- Rewrite to match r4_loop: (0, 0, 0 + (2n+2), 1, E n) ⊢* (0, 0, 0, 1+(2n+2), E n)
  rw [show (2 * n + 2 : ℕ) = 0 + (2 * n + 2) from by ring,
      show (1 : ℕ) = 1 from rfl]
  apply stepStar_trans (r4_loop (2 * n + 2) 0 1 (E n))
  -- Now at (0, 0, 0, 2n+3, E n)
  rw [show (1 : ℕ) + (2 * n + 2) = 2 * n + 3 from by ring]
  -- Phase 2: Middle init + loop
  rw [show 2 * n + 3 = (2 * n + 1) + 2 from by ring,
      show E n = (E n - 1) + 1 from by omega]
  apply stepStar_trans (middle_init (2 * n + 1) (E n - 1))
  rw [show 2 * n + 1 = 1 + 2 * n from by ring,
      show E n - 1 = (E n - 1 - n) + n from by omega]
  apply stepStar_trans (middle_loop n 0 1 (E n - 1 - n))
  rw [show 0 + 1 + n = n + 1 from by ring]
  -- Phase 3: Tail step
  rw [show E n - 1 - n = (E n - n - 2) + 1 from by omega]
  apply stepStar_trans (tail_step n (E n - n - 2))
  -- Phase 4: Climbing
  have h := climb_gen (n + 1) 0 (E n - n - 2)
  rw [show 3 * 0 + 3 + 2 * (n + 1) = 2 * n + 5 from by ring,
      show E n - n - 2 + 2 * 0 + 2 + 2 * (n + 1) = E n + n + 2 from by omega] at h
  rw [show 2 * (n + 1) + 3 = 2 * n + 5 from by ring,
      show E (n + 1) = E n + n + 2 from by rfl]
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * n + 3, 0, E n⟩) 0
  intro n
  exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_360
