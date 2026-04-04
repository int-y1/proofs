import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1647: [77/15, 28/3, 27/22, 5/7, 3/2]

Vector representation:
```
 0 -1 -1  1  1
 2 -1  0  1  0
-1  3  0  0 -1
 0  0  1 -1  0
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1647

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ a d e,
    ⟨a + k, 0, 3 * k, d, e + 1⟩ [fm]⊢* ⟨a, 0, 0, d + 3 * k, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by omega,
        show 3 * (k + 1) = ((3 * k + 1) + 1) + 1 from by omega]
    step fm; step fm; step fm
    rw [show 3 * k + 1 = (3 * k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih a (d + 3) (e + 2))
    ring_nf; finish

theorem r3r2_chain : ∀ k, ∀ a d,
    ⟨a + 1, 0, 0, d, k⟩ [fm]⊢* ⟨a + 5 * k + 1, 0, 0, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (a + 5) (d + 3))
    ring_nf; finish

theorem main_trans (a m : ℕ) :
    ⟨a + m + 2, 0, 3 * m + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 10 * m + 6, 0, 9 * m + 4, 0, 0⟩ := by
  have phase01 : ⟨a + m + 2, 0, 3 * m + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + m + 1, 0, 3 * m, 1, 1⟩ := by
    rw [show a + m + 2 = (a + m + 1) + 1 from by omega,
        show 3 * m + 1 = (3 * m) + 1 from by omega]
    step fm; step fm; finish
  have phase2 : ⟨a + m + 1, 0, 3 * m, 1, 1⟩ [fm]⊢* ⟨a + 1, 0, 0, 3 * m + 1, 2 * m + 1⟩ := by
    have h := r3r1_chain m (a + 1) 1 0
    simp at h
    rw [show a + 1 + m = a + m + 1 from by ring,
        show 1 + 3 * m = 3 * m + 1 from by ring] at h
    exact h
  have phase3 : ⟨a + 1, 0, 0, 3 * m + 1, 2 * m + 1⟩ [fm]⊢* ⟨a + 10 * m + 6, 0, 0, 9 * m + 4, 0⟩ := by
    have h := r3r2_chain (2 * m + 1) a (3 * m + 1)
    rw [show a + 5 * (2 * m + 1) + 1 = a + 10 * m + 6 from by ring,
        show 3 * m + 1 + 3 * (2 * m + 1) = 9 * m + 4 from by ring] at h
    exact h
  have phase4 : ⟨a + 10 * m + 6, 0, 0, 9 * m + 4, 0⟩ [fm]⊢* ⟨a + 10 * m + 6, 0, 9 * m + 4, 0, 0⟩ := by
    have h := r4_chain (9 * m + 4) (a + 10 * m + 6) 0
    simp at h; exact h
  exact stepPlus_stepStar_stepPlus
    (stepPlus_stepStar_stepPlus
      (stepPlus_stepStar_stepPlus phase01 phase2) phase3) phase4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + p.2 + 2, 0, 3 * p.2 + 1, 0, 0⟩) ⟨0, 0⟩
  intro ⟨a, m⟩
  refine ⟨⟨a + 7 * m + 3, 3 * m + 1⟩, ?_⟩
  show ⟨a + m + 2, 0, 3 * m + 1, 0, 0⟩ [fm]⊢⁺
    ⟨a + 7 * m + 3 + (3 * m + 1) + 2, 0, 3 * (3 * m + 1) + 1, 0, 0⟩
  rw [show a + 7 * m + 3 + (3 * m + 1) + 2 = a + 10 * m + 6 from by ring,
      show 3 * (3 * m + 1) + 1 = 9 * m + 4 from by ring]
  exact main_trans a m
