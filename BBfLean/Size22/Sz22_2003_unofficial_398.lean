import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #398: [20/3, 9/35, 1/20, 343/2, 3/7]

Vector representation:
```
 2 -1  1  0
 0  2 -1 -1
-2  0 -1  0
-1  0  0  3
 0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_398

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a, b, c+1, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+2, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+3⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- Phase A: (a+k, 0, 0, d) →* (a, 0, 0, d+3*k) by rule 4
theorem phaseA : ∀ k a d, ⟨a+k, 0, 0, d⟩ [fm]⊢* ⟨a, 0, 0, d+3*k⟩ := by
  intro k; induction k with
  | zero => intro a d; simp; exists 0
  | succ k ih =>
    intro a d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 3))
    ring_nf; finish

-- Phase B: (0, 0, 0, D+2) →* (6, 0, 2, D) in 5 steps
theorem phaseB (D : ℕ) : ⟨0, 0, 0, D+2⟩ [fm]⊢* ⟨6, 0, 2, D⟩ := by
  step fm; step fm; step fm; step fm; step fm
  finish

-- Phase C: inner loop — (A, 0, c+1, n) →* (A+4*n, 0, c+1+n, 0)
theorem phaseC : ∀ n A c, ⟨A, 0, c+1, n⟩ [fm]⊢* ⟨A+4*n, 0, c+1+n, 0⟩ := by
  intro n; induction n with
  | zero => intro A c; simp; exists 0
  | succ n ih =>
    intro A c
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 4) (c + 1))
    ring_nf; finish

-- Phase D: (A+2*c, 0, c, 0) →* (A, 0, 0, 0) by rule 3
theorem phaseD : ∀ c A, ⟨A+2*c, 0, c, 0⟩ [fm]⊢* ⟨A, 0, 0, 0⟩ := by
  intro c; induction c with
  | zero => intro A; simp; exists 0
  | succ c ih =>
    intro A
    rw [show A + 2 * (c + 1) = (A + 2 * c) + 2 from by ring]
    step fm
    exact ih A

-- Main transition: (a+1, 0, 0, 0) →⁺ (6*a+4, 0, 0, 0)
theorem main_trans (a : ℕ) : ⟨a+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨6*a+4, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 3*a+3⟩)
  · have h := phaseA (a+1) 0 0
    rw [show 0 + (a + 1) = a + 1 from by ring,
        show 0 + 3 * (a + 1) = 3*a+3 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨6, 0, 2, 3*a+1⟩)
  · rw [show 3*a+3 = (3*a+1) + 2 from by ring]; exact phaseB (3*a+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨12*a+10, 0, 3*a+3, 0⟩)
  · have h := phaseC (3*a+1) 6 1
    rw [show 6 + 4 * (3 * a + 1) = 12*a+10 from by ring,
        show 1 + 1 + (3 * a + 1) = 3*a+3 from by ring] at h
    exact h
  have h := phaseD (3*a+3) (6*a+4)
  rw [show (6*a+4) + 2 * (3*a+3) = 12*a+10 from by ring] at h
  exact stepStar_stepPlus h (by
    intro heq; have := congr_arg (fun q : Q => q.1) heq; simp at this; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a, q = ⟨a+1, 0, 0, 0⟩)
  · intro c ⟨a, hq⟩; subst hq
    exact ⟨⟨(6*a+3)+1, 0, 0, 0⟩, ⟨6*a+3, rfl⟩, by
      show ⟨a+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨6*a+4, 0, 0, 0⟩
      exact main_trans a⟩
  · exact ⟨0, rfl⟩

end Sz22_2003_unofficial_398
