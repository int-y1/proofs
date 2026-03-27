import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #171: [1/45, 7/5, 500/77, 3/7, 55/2]

Vector representation:
```
 0 -2 -1  0  0
 0  0 -1  1  0
 2  0  3 -1 -1
 0  1  0 -1  0
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_171

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c+3, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- Drain single step: Rule 5 then Rule 1
theorem drain_step : ⟨a+1, b+2, 0, 0, e⟩ [fm]⊢* (⟨a, b, 0, 0, e+1⟩ : Q) := by
  step fm; step fm; finish

-- Drain chain by induction on k
theorem drain : ⟨a+k, b+2*k, 0, 0, e⟩ [fm]⊢* (⟨a, b, 0, 0, e+k⟩ : Q) := by
  have h : ∀ k a e, ⟨a+k, b+2*k, 0, 0, e⟩ [fm]⊢* (⟨a, b, 0, 0, e+k⟩ : Q) := by
    intro k; induction' k with k ih <;> intro a e
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show a + (k + 1) = (a + k) + 1 from by ring]
    apply stepStar_trans (drain_step (b := b + 2 * k))
    apply stepStar_trans (ih a _)
    ring_nf; finish
  exact h k a e

-- Expand loop single step for b=0: Rule 3 then Rule 2 x3
theorem expand_loop_step_b0 : ⟨a, 0, 0, d+1, e+1⟩ [fm]⊢* (⟨a+2, 0, 0, d+3, e⟩ : Q) := by
  step fm; step fm; step fm; step fm; finish

-- Expand loop single step for b=1
theorem expand_loop_step_b1 : ⟨a, 1, 0, d+1, e+1⟩ [fm]⊢* (⟨a+2, 1, 0, d+3, e⟩ : Q) := by
  step fm; step fm; step fm; step fm; finish

-- Expand loop for b=0 by induction on e
theorem expand_loop_b0 : ⟨a, 0, 0, d+1, e⟩ [fm]⊢* (⟨a+2*e, 0, 0, d+2*e+1, 0⟩ : Q) := by
  have h : ∀ e a d, ⟨a, 0, 0, d+1, e⟩ [fm]⊢* (⟨a+2*e, 0, 0, d+2*e+1, 0⟩ : Q) := by
    intro e; induction' e with e ih <;> intro a d
    · exists 0
    apply stepStar_trans expand_loop_step_b0
    rw [show d + 3 = (d + 2) + 1 from by ring]
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact h e a d

-- Expand loop for b=1
theorem expand_loop_b1 : ⟨a, 1, 0, d+1, e⟩ [fm]⊢* (⟨a+2*e, 1, 0, d+2*e+1, 0⟩ : Q) := by
  have h : ∀ e a d, ⟨a, 1, 0, d+1, e⟩ [fm]⊢* (⟨a+2*e, 1, 0, d+2*e+1, 0⟩ : Q) := by
    intro e; induction' e with e ih <;> intro a d
    · exists 0
    apply stepStar_trans expand_loop_step_b1
    rw [show d + 3 = (d + 2) + 1 from by ring]
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact h e a d

-- d to b: Rule 4 repeated
theorem d_to_b : ⟨a, b, 0, d, 0⟩ [fm]⊢* (⟨a, b+d, 0, 0, 0⟩ : Q) := by
  have h : ∀ d b, ⟨a, b, 0, d, 0⟩ [fm]⊢* (⟨a, b+d, 0, 0, 0⟩ : Q) := by
    intro d; induction' d with d ih <;> intro b
    · exists 0
    step fm
    rw [show b + 1 = (b + 1) from rfl]
    apply stepStar_trans (ih _)
    ring_nf; finish
  exact h d b

-- Full expansion for b=0: (a+1, 0, 0, 0, e) ⊢⁺ (a+2*e+2, 2*e+3, 0, 0, 0)
-- Init (6 steps) + expand_loop + d_to_b
theorem expand_b0 : ⟨a+1, 0, 0, 0, e⟩ [fm]⊢⁺ (⟨a+2*e+2, 2*e+3, 0, 0, 0⟩ : Q) := by
  -- 6 init steps give ⊢⁺ to (a+2, 0, 0, 3, e)
  apply step_stepStar_stepPlus (by unfold fm; rfl : (⟨a+1, 0, 0, 0, e⟩ : Q) [fm]⊢ ⟨a, 0, 1, 0, e+1⟩)
  step fm; step fm; step fm; step fm; step fm
  -- Now at (a+2, 0, 0, 3, e). Apply expand_loop then d_to_b.
  rw [show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (expand_loop_b0 (d := 2))
  rw [show 2 + 2 * e + 1 = 2 * e + 3 from by ring,
      show a + 2 + 2 * e = a + 2 * e + 2 from by ring]
  apply stepStar_trans (d_to_b (b := 0) (d := 2 * e + 3))
  simp only [Nat.zero_add]; finish

-- Full expansion for b=1: (a+1, 1, 0, 0, e) ⊢⁺ (a+2*e+2, 2*e+4, 0, 0, 0)
theorem expand_b1 : ⟨a+1, 1, 0, 0, e⟩ [fm]⊢⁺ (⟨a+2*e+2, 2*e+4, 0, 0, 0⟩ : Q) := by
  apply step_stepStar_stepPlus (by unfold fm; rfl : (⟨a+1, 1, 0, 0, e⟩ : Q) [fm]⊢ ⟨a, 1, 1, 0, e+1⟩)
  step fm; step fm; step fm; step fm; step fm
  rw [show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (expand_loop_b1 (d := 2))
  rw [show 2 + 2 * e + 1 = 2 * e + 3 from by ring,
      show a + 2 + 2 * e = a + 2 * e + 2 from by ring]
  apply stepStar_trans (d_to_b (b := 1) (d := 2 * e + 3))
  rw [show 1 + (2 * e + 3) = 2 * e + 4 from by ring]; finish

-- Even cycle: (a+m+1, 2*m, 0, 0, 0) ⊢⁺ (a+2*m+2, 2*m+3, 0, 0, 0)
theorem even_cycle : ⟨a+m+1, 2*m, 0, 0, 0⟩ [fm]⊢⁺ (⟨a+2*m+2, 2*m+3, 0, 0, 0⟩ : Q) := by
  rw [show a + m + 1 = (a + 1) + m from by ring,
      show 2 * m = 0 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus (drain (b := 0) (k := m) (e := 0))
  simp only [Nat.zero_add]
  exact expand_b0

-- Odd cycle: (a+m+1, 2*m+1, 0, 0, 0) ⊢⁺ (a+2*m+2, 2*m+4, 0, 0, 0)
theorem odd_cycle : ⟨a+m+1, 2*m+1, 0, 0, 0⟩ [fm]⊢⁺ (⟨a+2*m+2, 2*m+4, 0, 0, 0⟩ : Q) := by
  rw [show a + m + 1 = (a + 1) + m from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus (drain (b := 1) (k := m) (e := 0))
  simp only [Nat.zero_add]
  exact expand_b1

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 3, 0, 0, 0⟩)
  · execute fm 9
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a b, q = ⟨a, b, 0, 0, 0⟩ ∧ 2 * a ≥ b + 1 ∧ b ≥ 3)
  · intro c ⟨a, b, hq, ha, hb⟩; subst hq
    rcases Nat.even_or_odd b with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- b even: b = m + m = 2*m
      rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m + 1 := ⟨a - m - 1, by omega⟩
      exact ⟨⟨a'+2*m+2, 2*m+3, 0, 0, 0⟩,
        ⟨a'+2*m+2, 2*m+3, rfl, by omega, by omega⟩, even_cycle⟩
    · -- b odd: b = 2*m + 1
      subst hm
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m + 1 := ⟨a - m - 1, by omega⟩
      exact ⟨⟨a'+2*m+2, 2*m+4, 0, 0, 0⟩,
        ⟨a'+2*m+2, 2*m+4, rfl, by omega, by omega⟩, odd_cycle⟩
  · exact ⟨2, 3, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_171
