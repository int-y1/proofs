import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #380: [2/15, 99/14, 125/2, 7/11, 33/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  3  0  0
 0  0  0  1 -1
 0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_380

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

def tri : ℕ → ℕ
  | 0 => 0
  | n + 1 => tri n + n

theorem a_to_c : ∀ j a c e,
    ⟨a + j, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 3 * j, 0, e⟩ := by
  intro j; induction j with
  | zero => intro a c e; exists 0
  | succ j ih =>
    intro a c e
    rw [show a + (j + 1) = (a + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    rw [show (c + 3) + 3 * j = c + 3 * (j + 1) from by ring]
    finish

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

theorem r5_step : ∀ c d,
    ⟨0, 0, c + 1, d, 0⟩ [fm]⊢* ⟨0, 1, c, d, 1⟩ := by
  intro c d; step fm; finish

theorem first_iter : ∀ c d,
    ⟨0, 1, c + 1, d + 1, 1⟩ [fm]⊢* ⟨0, 2, c, d, 2⟩ := by
  intro c d; step fm; step fm; finish

theorem middle_iter_one : ∀ k c d e,
    ⟨k, 2, c + 2, d + 1, e⟩ [fm]⊢* ⟨k + 1, 2, c, d, e + 1⟩ := by
  intro k c d e; step fm; step fm; step fm; ring_nf; finish

theorem middle_iter : ∀ j k c d e,
    ⟨k, 2, c + 2 * j, d + j, e⟩ [fm]⊢* ⟨k + j, 2, c, d, e + j⟩ := by
  intro j; induction j with
  | zero => intro k c d e; exists 0
  | succ j ih =>
    intro k c d e
    rw [show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring,
        show d + (j + 1) = (d + j) + 1 from by ring]
    apply stepStar_trans (middle_iter_one _ _ _ _)
    apply stepStar_trans (ih _ _ _ _)
    rw [show (k + 1) + j = k + (j + 1) from by ring,
        show (e + 1) + j = e + (j + 1) from by ring]
    finish

theorem final_r1s : ∀ k c e,
    ⟨k, 2, c + 2, 0, e⟩ [fm]⊢* ⟨k + 2, 0, c, 0, e⟩ := by
  intro k c e; step fm; step fm; ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, tri n, 0, n + 2⟩ [fm]⊢⁺ ⟨n + 3, 0, tri (n + 1), 0, n + 3⟩ := by
  show ⟨n + 2, 0, tri n, 0, n + 2⟩ [fm]⊢⁺ ⟨n + 3, 0, tri n + n, 0, n + 3⟩
  -- Phase 1: first R3 step (for ⊢⁺), then a_to_c for remaining
  apply step_stepStar_stepPlus
  · show fm ⟨n + 2, 0, tri n, 0, n + 2⟩ = some ⟨n + 1, 0, tri n + 3, 0, n + 2⟩; rfl
  -- State: (n+1, 0, tri n + 3, 0, n+2)
  -- Phase 1 continued: a_to_c (n+1 more steps)
  apply stepStar_trans
  · have h := a_to_c (n + 1) 0 (tri n + 3) (n + 2)
    simp only [show 0 + (n + 1) = n + 1 from by ring] at h
    exact h
  -- State: (0, 0, tri n + 3 + 3*(n+1), 0, n+2)
  -- Phase 2: e_to_d
  apply stepStar_trans
  · have h := e_to_d (n + 2) (tri n + 3 + 3 * (n + 1)) 0 0
    simp only [show 0 + (n + 2) = n + 2 from by ring] at h
    exact h
  -- State: (0, 0, tri n + 3 + 3*(n+1), n+2, 0)
  -- Phase 3: R5 step
  apply stepStar_trans
  · have h := r5_step (tri n + 2 + 3 * (n + 1)) (n + 2)
    simp only [show (tri n + 2 + 3 * (n + 1)) + 1 = tri n + 3 + 3 * (n + 1) from by ring] at h
    exact h
  -- State: (0, 1, tri n + 2 + 3*(n+1), n+2, 1)
  -- Phase 4: first_iter
  apply stepStar_trans
  · have h := first_iter (tri n + 1 + 3 * (n + 1)) (n + 1)
    simp only [show (tri n + 1 + 3 * (n + 1)) + 1 = tri n + 2 + 3 * (n + 1) from by ring,
               show (n + 1) + 1 = n + 2 from by ring] at h
    exact h
  -- State: (0, 2, tri n + 1 + 3*(n+1), n+1, 2)
  -- Phase 5: middle_iter (n+1 iterations)
  apply stepStar_trans
  · have h := middle_iter (n + 1) 0 (tri n + n + 2) 0 2
    simp only [show (tri n + n + 2) + 2 * (n + 1) = tri n + 1 + 3 * (n + 1) from by ring,
               show 0 + (n + 1) = n + 1 from by ring,
               show 2 + (n + 1) = n + 3 from by ring] at h
    exact h
  -- State: (n+1, 2, tri n + n + 2, 0, n+3)
  -- Phase 6: final_r1s
  have h := final_r1s (n + 1) (tri n + n) (n + 3)
  simp only [show (n + 1) + 2 = n + 3 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, tri n, 0, n + 2⟩) 0
  intro n
  exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_380
