import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #367: [2/15, 63/2, 11/3, 125/77, 3/55]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0  1  0
 0 -1  0  0  1
 0  0  3 -1 -1
 0  1 -1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_367

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1: drain b via rule 3: (0, b+j, 0, d, e) ->* (0, b, 0, d, e+j)
theorem b_drain : ∀ j b d e,
    ⟨0, b+j, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e+j⟩ := by
  intro j; induction j with
  | zero => intro b d e; exists 0
  | succ j ih =>
    intro b d e
    rw [show b + (j + 1) = (b + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    rw [show (e + 1) + j = e + (j + 1) from by ring]
    finish

-- Phase 2: convert d,e pairs to c: (0, 0, c, d+j, e+j) ->* (0, 0, c+3*j, d, e)
theorem de_to_c : ∀ j c d e,
    ⟨0, 0, c, d+j, e+j⟩ [fm]⊢* ⟨0, 0, c+3*j, d, e⟩ := by
  intro j; induction j with
  | zero => intro c d e; exists 0
  | succ j ih =>
    intro c d e
    rw [show d + (j + 1) = (d + j) + 1 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    rw [show (c + 3) + 3 * j = c + 3 * (j + 1) from by ring]
    finish

-- Phase 5: crunch triple: (a, 2, c+2, d, 0) ->* (a+1, 2, c, d+1, 0)
-- Note: b must be 0 for rule2 to fire after two rule1 steps
theorem crunch_step : ∀ a c d,
    ⟨a, 2, c+2, d, 0⟩ [fm]⊢* ⟨a+1, 2, c, d+1, 0⟩ := by
  intro a c d
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨a, 2, c+2, d, 0⟩ = some ⟨a+1, 1, c+1, d, 0⟩ from rfl)
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨a+1, 1, c+1, d, 0⟩ = some ⟨a+1+1, 0, c, d, 0⟩ from rfl)
  -- Now b=0, c is free. Rule1 needs b+1 so doesn't match. Rule2 matches a+1+1 as (a+1).succ.
  exact step_stepStar (show fm ⟨a+1+1, 0, c, d, 0⟩ = some ⟨a+1, 2, c, d+1, 0⟩ from rfl)

-- Phase 5: crunch iteration: (a, 2, c+2*j, d, 0) ->* (a+j, 2, c, d+j, 0)
theorem crunch_iter : ∀ j a c d,
    ⟨a, 2, c+2*j, d, 0⟩ [fm]⊢* ⟨a+j, 2, c, d+j, 0⟩ := by
  intro j; induction j with
  | zero => intro a c d; simp; exists 0
  | succ j ih =>
    intro a c d
    rw [show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring]
    apply stepStar_trans (crunch_step _ _ _)
    apply stepStar_trans (ih _ _ _)
    rw [show (a + 1) + j = a + (j + 1) from by ring,
        show (d + 1) + j = d + (j + 1) from by ring]
    finish

-- Phase 6: drain a via rule 2: (a+j, b, 0, d, 0) ->* (a, b+2*j, 0, d+j, 0)
theorem a_drain : ∀ j a b d,
    ⟨a+j, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+2*j, 0, d+j, 0⟩ := by
  intro j; induction j with
  | zero => intro a b d; simp; exists 0
  | succ j ih =>
    intro a b d
    rw [show a + (j + 1) = (a + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    rw [show (b + 2) + 2 * j = b + 2 * (j + 1) from by ring,
        show (d + 1) + j = d + (j + 1) from by ring]
    finish

-- Crunch tail when c=1: (a, 2, 1, d, 0) ->* (a, 3, 0, d+1, 0)
theorem crunch_tail : ∀ a d,
    ⟨a, 2, 1, d, 0⟩ [fm]⊢* ⟨a, 3, 0, d+1, 0⟩ := by
  intro a d
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨a, 2, 1, d, 0⟩ = some ⟨a+1, 1, 0, d, 0⟩ from rfl)
  exact step_stepStar (show fm ⟨a+1, 1, 0, d, 0⟩ = some ⟨a, 3, 0, d+1, 0⟩ from rfl)

-- Main transition for even n: n = 2*m
-- (0, 2*m+2, 0, 2*m+1, 0) ->+ (0, 6*m+3, 0, 6*m+2, 0)
theorem main_trans_even (m : ℕ) :
    ⟨0, 2*m+2, 0, 2*m+1, 0⟩ [fm]⊢⁺ ⟨0, 6*m+3, 0, 6*m+2, 0⟩ := by
  -- Phase 1: drain b
  apply stepStar_stepPlus_stepPlus
  · have h := b_drain (2*m+2) 0 (2*m+1) 0
    simp only [(by ring : 0 + (2*m+2) = 2*m+2)] at h
    exact h
  -- Phase 2: de_to_c
  apply stepStar_stepPlus_stepPlus
  · have h := de_to_c (2*m+1) 0 0 1
    simp only [(by ring : 0 + (2*m+1) = 2*m+1),
               (by ring : 1 + (2*m+1) = 2*m+2),
               (by ring : 0 + 3*(2*m+1) = 6*m+3)] at h
    exact h
  -- Phase 3: rule 5
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 6*m+3, 0, 1⟩ = some ⟨0, 1, 6*m+2, 0, 0⟩
    simp [fm]
  -- Phase 4: rule 1 + rule 2
  apply stepStar_trans
  · show ⟨0, 1, 6*m+2, 0, 0⟩ [fm]⊢* ⟨0, 2, 6*m+1, 1, 0⟩
    step fm; step fm; finish
  -- Phase 5: crunch 3m groups
  apply stepStar_trans
  · have h := crunch_iter (3*m) 0 1 1
    rw [show 1 + 2*(3*m) = 6*m+1 from by ring,
        show 0 + 3*m = 3*m from by ring,
        show 1 + 3*m = 3*m+1 from by ring] at h
    exact h
  -- Phase 5b: crunch tail (c=1)
  apply stepStar_trans
  · exact crunch_tail (3*m) (3*m+1)
  -- Phase 6: drain a
  have h := a_drain (3*m) 0 3 (3*m+2)
  rw [show 0 + 3*m = 3*m from by ring,
      show 3 + 2*(3*m) = 6*m+3 from by ring,
      show (3*m+2) + 3*m = 6*m+2 from by ring] at h
  exact h

-- Main transition for odd n: n = 2*m+1
-- (0, 2*m+3, 0, 2*m+2, 0) ->+ (0, 6*m+6, 0, 6*m+5, 0)
theorem main_trans_odd (m : ℕ) :
    ⟨0, 2*m+3, 0, 2*m+2, 0⟩ [fm]⊢⁺ ⟨0, 6*m+6, 0, 6*m+5, 0⟩ := by
  -- Phase 1: drain b
  apply stepStar_stepPlus_stepPlus
  · have h := b_drain (2*m+3) 0 (2*m+2) 0
    simp only [(by ring : 0 + (2*m+3) = 2*m+3)] at h
    exact h
  -- Phase 2: de_to_c
  apply stepStar_stepPlus_stepPlus
  · have h := de_to_c (2*m+2) 0 0 1
    simp only [(by ring : 0 + (2*m+2) = 2*m+2),
               (by ring : 1 + (2*m+2) = 2*m+3),
               (by ring : 0 + 3*(2*m+2) = 6*m+6)] at h
    exact h
  -- Phase 3: rule 5
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 6*m+6, 0, 1⟩ = some ⟨0, 1, 6*m+5, 0, 0⟩
    simp [fm]
  -- Phase 4: rule 1 + rule 2
  apply stepStar_trans
  · show ⟨0, 1, 6*m+5, 0, 0⟩ [fm]⊢* ⟨0, 2, 6*m+4, 1, 0⟩
    step fm; step fm; finish
  -- Phase 5: crunch (3m+2) groups
  apply stepStar_trans
  · have h := crunch_iter (3*m+2) 0 0 1
    rw [show 0 + 2*(3*m+2) = 6*m+4 from by ring,
        show 0 + (3*m+2) = 3*m+2 from by ring,
        show 1 + (3*m+2) = 3*m+3 from by ring] at h
    exact h
  -- Phase 6: drain a
  have h := a_drain (3*m+2) 0 2 (3*m+3)
  rw [show 0 + (3*m+2) = 3*m+2 from by ring,
      show 2 + 2*(3*m+2) = 6*m+6 from by ring,
      show (3*m+3) + (3*m+2) = 6*m+5 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, n+2, 0, n+1, 0⟩) 0
  intro n
  refine ⟨3*n+1, ?_⟩
  show (0, n + 2, 0, n + 1, 0) [fm]⊢⁺ (0, 3 * n + 1 + 2, 0, 3 * n + 1 + 1, 0)
  rw [show 3 * n + 1 + 2 = 3*n+3 from by ring,
      show 3 * n + 1 + 1 = 3*n+2 from by ring]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    show (0, m + m + 2, 0, m + m + 1, 0) [fm]⊢⁺ (0, 3 * (m + m) + 3, 0, 3 * (m + m) + 2, 0)
    rw [show m + m = 2*m from by ring,
        show 3 * (2*m) + 3 = 6*m+3 from by ring,
        show 3 * (2*m) + 2 = 6*m+2 from by ring]
    exact main_trans_even m
  · subst hm
    show (0, 2 * m + 1 + 2, 0, 2 * m + 1 + 1, 0) [fm]⊢⁺ (0, 3 * (2 * m + 1) + 3, 0, 3 * (2 * m + 1) + 2, 0)
    rw [show 2*m+1+2 = 2*m+3 from by ring,
        show 2*m+1+1 = 2*m+2 from by ring,
        show 3*(2*m+1)+3 = 6*m+6 from by ring,
        show 3*(2*m+1)+2 = 6*m+5 from by ring]
    exact main_trans_odd m

end Sz22_2003_unofficial_367
