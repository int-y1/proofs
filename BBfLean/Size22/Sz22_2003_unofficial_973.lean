import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #973: [4/15, 33/14, 5/2, 7/11, 88/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 3  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_973

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d, e+1⟩
  | _ => none

theorem a_to_c : ∀ k, ∀ c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

theorem e_to_d : ∀ k, ∀ c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e, ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c d (e + 1))
    ring_nf; finish

theorem main_trans : ⟨n + 3, 0, n, 0, n + 1⟩ [fm]⊢⁺ ⟨n + 4, 0, n + 1, 0, n + 2⟩ := by
  have h1 : ⟨n + 3, 0, n, 0, n + 1⟩ [fm]⊢* ⟨0, 0, 2 * n + 3, 0, n + 1⟩ := by
    have := a_to_c (n + 3) n (n + 1)
    rw [show n + (n + 3) = 2 * n + 3 from by ring] at this
    exact this
  have h2 : ⟨0, 0, 2 * n + 3, 0, n + 1⟩ [fm]⊢* ⟨0, 0, 2 * n + 3, n + 1, 0⟩ := by
    have := e_to_d (n + 1) (2 * n + 3) 0
    rw [show 0 + (n + 1) = n + 1 from by ring] at this
    exact this
  have h3 : ⟨0, 0, 2 * n + 3, n + 1, 0⟩ [fm]⊢ ⟨3, 0, 2 * n + 2, n + 1, 1⟩ := by
    rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
    simp [fm]
  have h4 : ⟨3, 0, 2 * n + 2, n + 1, 1⟩ [fm]⊢* ⟨n + 4, 0, n + 1, 0, n + 2⟩ := by
    have := r2r1_chain (n + 1) 2 (n + 1) 0 1
    simp only [show 2 + (n + 1) + 1 = n + 4 from by ring,
               show 1 + (n + 1) = n + 2 from by ring,
               show (n + 1) + (n + 1) = 2 * n + 2 from by ring,
               show 0 + (n + 1) = n + 1 from by ring,
               show 2 + 1 = 3 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (step_stepStar_stepPlus h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 3, 0, n, 0, n + 1⟩) 0
  intro n; exists n + 1; exact main_trans
