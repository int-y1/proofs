import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1653: [77/15, 28/3, 9/22, 5/7, 9/2]

Vector representation:
```
 0 -1 -1  1  1
 2 -1  0  1  0
-1  2  0  0 -1
 0  0  1 -1  0
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1653

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

theorem r3r1r1_chain : ∀ k, ∀ a d e,
    ⟨a + k, 0, 2 * k, d, e + 1⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by omega,
        show 2 * (k + 1) = (2 * k + 1) + 1 from by omega]
    step fm; step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih a (d + 2) (e + 1))
    ring_nf; finish

theorem r3r2r2_chain : ∀ k, ∀ a d,
    ⟨a + 1, 0, 0, d, k⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (d + 2))
    ring_nf; finish

theorem main_trans (m F : ℕ) :
    ⟨2 * m + F + 4, 0, 2 * m + 2, 0, 0⟩ [fm]⊢⁺ ⟨4 * m + F + 9, 0, 4 * m + 6, 0, 0⟩ := by
  have phase01 : ⟨2 * m + F + 4, 0, 2 * m + 2, 0, 0⟩ [fm]⊢⁺ ⟨2 * m + F + 3, 0, 2 * m, 2, 2⟩ := by
    rw [show 2 * m + F + 4 = (2 * m + F + 3) + 1 from by omega,
        show 2 * m + 2 = (2 * m + 1) + 1 from by omega]
    step fm; step fm
    rw [show 2 * m + 1 = (2 * m) + 1 from by omega]
    step fm; finish
  have phase2 : ⟨2 * m + F + 3, 0, 2 * m, 2, 2⟩ [fm]⊢* ⟨m + F + 3, 0, 0, 2 * m + 2, m + 2⟩ := by
    have h := r3r1r1_chain m (m + F + 3) 2 1
    rw [show m + F + 3 + m = 2 * m + F + 3 from by ring,
        show 2 + 2 * m = 2 * m + 2 from by ring,
        show 1 + m + 1 = m + 2 from by ring] at h
    exact h
  have phase3 : ⟨m + F + 3, 0, 0, 2 * m + 2, m + 2⟩ [fm]⊢* ⟨4 * m + F + 9, 0, 0, 4 * m + 6, 0⟩ := by
    have h := r3r2r2_chain (m + 2) (m + F + 2) (2 * m + 2)
    rw [show m + F + 2 + 1 = m + F + 3 from by ring,
        show m + F + 2 + 3 * (m + 2) + 1 = 4 * m + F + 9 from by ring,
        show 2 * m + 2 + 2 * (m + 2) = 4 * m + 6 from by ring] at h
    exact h
  have phase4 : ⟨4 * m + F + 9, 0, 0, 4 * m + 6, 0⟩ [fm]⊢* ⟨4 * m + F + 9, 0, 4 * m + 6, 0, 0⟩ := by
    have h := r4_chain (4 * m + 6) (4 * m + F + 9) 0
    simp at h; exact h
  exact stepPlus_stepStar_stepPlus
    (stepPlus_stepStar_stepPlus
      (stepPlus_stepStar_stepPlus phase01 phase2) phase3) phase4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 2, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, F⟩ ↦ ⟨2 * m + F + 4, 0, 2 * m + 2, 0, 0⟩) ⟨0, 0⟩
  intro ⟨m, F⟩
  refine ⟨⟨2 * m + 2, F + 1⟩, ?_⟩
  show ⟨2 * m + F + 4, 0, 2 * m + 2, 0, 0⟩ [fm]⊢⁺
    ⟨2 * (2 * m + 2) + (F + 1) + 4, 0, 2 * (2 * m + 2) + 2, 0, 0⟩
  rw [show 2 * (2 * m + 2) + (F + 1) + 4 = 4 * m + F + 9 from by ring,
      show 2 * (2 * m + 2) + 2 = 4 * m + 6 from by ring]
  exact main_trans m F
