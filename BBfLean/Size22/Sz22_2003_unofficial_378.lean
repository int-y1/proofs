import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #378: [2/15, 99/14, 125/2, 7/11, 21/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  3  0  0
 0  0  0  1 -1
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_378

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem e_to_d : ∀ j c d e,
    ⟨0, 0, c, d, e + j⟩ [fm]⊢* ⟨0, 0, c, d + j, e⟩ := by
  intro j; induction j with
  | zero => intro c d e; exists 0
  | succ j ih =>
    intro c d e
    rw [show e + (j + 1) = (e + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    rw [show (d + 1) + j = d + (j + 1) from by ring]
    finish

theorem first_step : ∀ c d,
    ⟨0, 0, c + 2, d, 0⟩ [fm]⊢* ⟨0, 2, c, d, 1⟩ := by
  intro c d
  step fm; step fm; step fm
  ring_nf; finish

theorem inner_cycle_one : ∀ k c d e,
    ⟨k, 2, c + 2, d + 1, e⟩ [fm]⊢* ⟨k + 1, 2, c, d, e + 1⟩ := by
  intro k c d e
  step fm; step fm; step fm
  ring_nf; finish

theorem inner_cycle_iter : ∀ j k c d e,
    ⟨k, 2, c + 2 * j, d + j, e⟩ [fm]⊢* ⟨k + j, 2, c, d, e + j⟩ := by
  intro j; induction j with
  | zero => intro k c d e; simp; exists 0
  | succ j ih =>
    intro k c d e
    rw [show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring,
        show d + (j + 1) = (d + j) + 1 from by ring]
    apply stepStar_trans (inner_cycle_one _ _ _ _)
    apply stepStar_trans (ih _ _ _ _)
    rw [show (k + 1) + j = k + (j + 1) from by ring,
        show (e + 1) + j = e + (j + 1) from by ring]
    finish

theorem tail_step : ∀ d c e,
    ⟨d, 2, c + 2, 0, e⟩ [fm]⊢* ⟨d + 2, 0, c, 0, e⟩ := by
  intro d c e
  step fm; step fm
  ring_nf; finish

theorem rule3_unwind : ∀ j a c e,
    ⟨a + j, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 3 * j, 0, e⟩ := by
  intro j; induction j with
  | zero => intro a c e; simp; exists 0
  | succ j ih =>
    intro a c e
    rw [show a + (j + 1) = (a + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    rw [show (c + 3) + 3 * j = c + 3 * (j + 1) from by ring]
    finish

theorem main_trans (c e : ℕ) :
    ⟨0, 0, c + 2 * e + 4, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c + 3 * e + 6, 0, e + 1⟩ := by
  -- Phase 1: transfer e to d
  -- e_to_d e ... gives: (0,0,C,0,0+e) ⊢* (0,0,C,0+e,0)
  apply stepStar_stepPlus_stepPlus
  · have h := e_to_d e (c + 2 * e + 4) 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 2a: first step
  apply stepStar_stepPlus_stepPlus
  · have h := first_step (c + 2 * e + 2) e
    rw [show (c + 2 * e + 2) + 2 = c + 2 * e + 4 from by ring] at h
    exact h
  -- Phase 2b: inner cycle (e iterations)
  apply stepStar_stepPlus_stepPlus
  · have h := inner_cycle_iter e 0 (c + 2) 0 1
    simp only [Nat.zero_add] at h
    rw [show (c + 2) + 2 * e = c + 2 * e + 2 from by ring,
        show 1 + e = e + 1 from by ring] at h
    exact h
  -- Phase 2c + Phase 3: tail step and rule3 unwind
  apply step_stepStar_stepPlus
  · show fm ⟨e, 2, c + 2, 0, e + 1⟩ = some ⟨e + 1, 1, c + 1, 0, e + 1⟩; rfl
  apply stepStar_trans
  · show ⟨e + 1, 1, c + 1, 0, e + 1⟩ [fm]⊢* ⟨e + 2, 0, c, 0, e + 1⟩
    step fm; finish
  have h := rule3_unwind (e + 2) 0 c (e + 1)
  simp only [Nat.zero_add] at h
  rw [show c + 3 * (e + 2) = c + 3 * e + 6 from by ring] at h
  exact h

theorem main_trans' (c e : ℕ) :
    ⟨0, 0, c + 2 * e + 4, 0, e⟩ [fm]⊢⁺ ⟨0, 0, (c + e) + 2 * (e + 1) + 4, 0, e + 1⟩ := by
  have h := main_trans c e
  rw [show (c + e) + 2 * (e + 1) + 4 = c + 3 * e + 6 from by ring]
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 8, 0, 2⟩) (by execute fm 20)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, p.1 + 2 * p.2 + 4, 0, p.2⟩) ⟨0, 2⟩
  intro ⟨c, e⟩
  exact ⟨⟨c + e, e + 1⟩, main_trans' c e⟩

end Sz22_2003_unofficial_378
