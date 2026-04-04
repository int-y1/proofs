import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1841: [9/20, 44/21, 49/2, 5/11, 3/7]

Vector representation:
```
-2  2 -1  0  0
 2 -1  0 -1  1
-1  0  0  2  0
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1841

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+2, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem a_to_d : ∀ k a d, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih
  · intro a d; exists 0
  · intro a d
    have h1 : fm ⟨a + k + 1, 0, 0, d, e⟩ = some ⟨a + k, 0, 0, d + 2, e⟩ := by simp [fm]
    rw [show a + (k + 1) = a + k + 1 from by ring]
    apply stepStar_trans (step_stepStar h1)
    rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    exact ih a (d + 2)

theorem e_to_c : ∀ k c e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih
  · intro c e; exists 0
  · intro c e
    have h1 : fm ⟨0, 0, c, d, e + k + 1⟩ = some ⟨0, 0, c + 1, d, e + k⟩ := by simp [fm]
    rw [show e + (k + 1) = e + k + 1 from by ring]
    apply stepStar_trans (step_stepStar h1)
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    exact ih (c + 1) e

theorem r1r2_chain : ∀ k j c d e, ⟨2, j, c + k, d + k, e⟩ [fm]⊢* ⟨2, j + k, c, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro j c d e; exists 0
  · intro j c d e
    have h1 : fm ⟨2, j, c + k + 1, d + k + 1, e⟩ = some ⟨0, j + 2, c + k, d + k + 1, e⟩ := by simp [fm]
    have h2 : fm ⟨0, j + 2, c + k, d + k + 1, e⟩ = some ⟨2, j + 1, c + k, d + k, e + 1⟩ := by simp [fm]
    rw [show c + (k + 1) = c + k + 1 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    apply stepStar_trans (step_stepStar h1)
    apply stepStar_trans (step_stepStar h2)
    rw [show j + (k + 1) = (j + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih (j + 1) c d (e + 1)

theorem r2_chain : ∀ k a b d e, ⟨a, b + k, 0, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a b d e; exists 0
  · intro a b d e
    have h1 : fm ⟨a, b + k + 1, 0, d + k + 1, e⟩ = some ⟨a + 2, b + k, 0, d + k, e + 1⟩ := by simp [fm]
    rw [show b + (k + 1) = b + k + 1 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    apply stepStar_trans (step_stepStar h1)
    rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih (a + 2) b d (e + 1)

theorem main_trans : ⟨n + 2, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨2 * n + 4, 0, 0, 0, 2 * n + 3⟩ := by
  have h1 : fm ⟨n + 2, 0, 0, 0, n + 1⟩ = some ⟨n + 1, 0, 0, 2, n + 1⟩ := by simp [fm]
  apply step_stepStar_stepPlus h1
  have p1 : ⟨n + 1, 0, 0, 2, n + 1⟩ [fm]⊢* ⟨0, 0, 0, 2 * n + 4, n + 1⟩ := by
    have := a_to_d (n + 1) 0 2 (e := n + 1)
    simp at this; rw [show 2 + 2 * (n + 1) = 2 * n + 4 from by ring] at this; exact this
  apply stepStar_trans p1
  have p2 : ⟨0, 0, 0, 2 * n + 4, n + 1⟩ [fm]⊢* ⟨0, 0, n + 1, 2 * n + 4, 0⟩ := by
    have := e_to_c (n + 1) 0 0 (d := 2 * n + 4)
    simp at this; exact this
  apply stepStar_trans p2
  have h5 : fm ⟨0, 0, n + 1, 2 * n + 4, 0⟩ = some ⟨0, 1, n + 1, 2 * n + 3, 0⟩ := by simp [fm]
  have h6 : fm ⟨0, 1, n + 1, 2 * n + 3, 0⟩ = some ⟨2, 0, n + 1, 2 * n + 2, 1⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar h5)
  apply stepStar_trans (step_stepStar h6)
  have p3a : ⟨2, 0, n + 1, 2 * n + 2, 1⟩ [fm]⊢* ⟨2, n + 1, 0, n + 1, n + 2⟩ := by
    have := r1r2_chain (n + 1) 0 0 (n + 1) 1
    simp at this
    rw [show (n + 1) + (n + 1) = 2 * n + 2 from by ring,
        show 1 + (n + 1) = n + 2 from by ring] at this
    exact this
  apply stepStar_trans p3a
  have p3b : ⟨2, n + 1, 0, n + 1, n + 2⟩ [fm]⊢* ⟨2 * n + 4, 0, 0, 0, 2 * n + 3⟩ := by
    have := r2_chain (n + 1) 2 0 0 (n + 2)
    simp at this
    rw [show 2 + 2 * (n + 1) = 2 * n + 4 from by ring,
        show n + 2 + (n + 1) = 2 * n + 3 from by ring] at this
    exact this
  exact p3b

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, n + 1⟩) 0
  intro n; exists 2 * n + 2
  exact main_trans
