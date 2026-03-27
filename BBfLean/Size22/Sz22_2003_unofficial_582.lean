import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #582: [35/6, 11/2, 4/55, 3/7, 84/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 2  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_582

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c, d+1, e⟩
  | _ => none

-- Phase 1: drain c using R3,R2,R2 rounds
theorem drain_ce : ∀ k e, ⟨(0:ℕ), (0:ℕ), k, d, e + 1⟩ [fm]⊢* ⟨0, 0, 0, d, e + k + 1⟩ := by
  intro k; induction' k with k h <;> intro e
  · exists 0
  step fm; step fm; step fm
  have := h (e + 1)
  rw [show (e + 1) + k + 1 = e + (k + 1) + 1 from by ring] at this
  exact this

-- Phase 2: drain d to b
theorem d_to_b : ∀ k b, ⟨(0:ℕ), b, (0:ℕ), d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  have := h (b + 1)
  rw [show (b + 1) + k = b + (k + 1) from by ring] at this
  exact this

-- Phase 3: R1,R1,R3 chain
theorem r1r1r3_chain : ∀ k c d, ⟨(2:ℕ), b + 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  have := h (c + 1) (d + 1 + 1)
  rw [show (c + 1) + k = c + (k + 1) from by ring,
      show (d + 1 + 1) + 2 * k = d + 2 * (k + 1) from by ring] at this
  exact this

-- Full cycle from (1, 0, n, 2n, 0) to (0, 0, 0, 2n, n+1)
theorem phase1 : ⟨1, 0, n, 2 * n, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * n, n + 1⟩ := by
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  have := drain_ce n 0 (d := 2 * n)
  rw [show (0:ℕ) + 1 = 1 from rfl, show 0 + n + 1 = n + 1 from by ring] at this
  exact this

-- From (0, 0, 0, 2n, n+1) to (0, 2n, 0, 0, n+1)
theorem phase2 : ⟨0, 0, 0, 2 * n, n + 1⟩ [fm]⊢* ⟨0, 2 * n, 0, 0, n + 1⟩ := by
  have := d_to_b (2 * n) 0 (d := 0) (e := n + 1)
  rw [Nat.zero_add] at this
  exact this

-- From (0, 2n, 0, 0, n+1) to (1, 0, n+1, 2(n+1), 0)
theorem phase3 : ⟨0, 2 * n, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨1, 0, n + 1, 2 * (n + 1), 0⟩ := by
  -- R5: (0, 2n, 0, 0, n+1) → (2, 2n+1, 0, 1, n)
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- r1r1r3_chain: (2, 1+2*n, 0, 1, 0+n) ⊢* (2, 1, 0+n, 1+2*n, 0)
  -- After step fm (R5), goal is: (0+2, 2*n+1, 0, 0+1, n) ⊢* (1, 0, n+1, 2*(n+1), 0)
  simp only [Nat.zero_add]
  rw [show 2 * n + 1 = 1 + 2 * n from by ring]
  have h3 := r1r1r3_chain n 0 1 (b := 1) (e := 0)
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  -- goal: (2, 1, n, 1+2*n, 0) ⊢* (1, 0, n+1, 2*(n+1), 0)
  -- need d = 1+2*n to be in successor form for R1 match
  rw [show 1 + 2 * n = 2 * n + 1 from by ring]
  -- R1: (2, 1, n, 2*n+1, 0) → (1, 0, n+1, 2*n+2, 0)
  apply step_stepStar (by unfold fm; rfl)

-- Main transition
theorem main_trans : ⟨1, 0, n, 2 * n, 0⟩ [fm]⊢⁺ ⟨1, 0, n + 1, 2 * (n + 1), 0⟩ :=
  stepPlus_stepStar_stepPlus (stepPlus_stepStar_stepPlus phase1 phase2) (stepPlus_stepStar phase3)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, n, 2 * n, 0⟩) 0
  intro n; exists n + 1; exact main_trans
