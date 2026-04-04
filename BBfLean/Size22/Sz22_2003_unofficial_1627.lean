import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1627: [77/15, 26/3, 18/91, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1  0
 1 -1  0  0  0  1
 1  2  0 -1  0 -1
 0  0  1  0 -1  0
-1  1  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1627

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a+1, b+2, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ a c f,
    ⟨a, 0, c, 0, k, f⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a c f
  · ring_nf; finish
  · step fm
    apply stepStar_trans (ih a (c + 1) f)
    ring_nf; finish

theorem inner_loop : ∀ k, ∀ A c d E F,
    ⟨A, 2, c + 2 * k, d, E, F + k⟩ [fm]⊢* ⟨A + k, 2, c, d + k, E + 2 * k, F⟩ := by
  intro k; induction' k with k ih <;> intro A c d E F
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show F + (k + 1) = (F + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 1) c (d + 1) (E + 2) F)
    ring_nf; finish

theorem even_remainder : ∀ A d E F,
    ⟨A, 2, 1, d, E, F + 1⟩ [fm]⊢* ⟨A + 1, 0, 0, d + 1, E + 1, F + 2⟩ := by
  intro A d E F
  step fm; step fm; finish

theorem odd_remainder : ∀ A d E F,
    ⟨A, 2, 0, d, E, F⟩ [fm]⊢* ⟨A + 2, 0, 0, d, E, F + 2⟩ := by
  intro A d E F
  step fm; step fm; finish

theorem drain : ∀ k, ∀ A E F,
    ⟨A, 0, 0, k, E, F + 1⟩ [fm]⊢* ⟨A + 3 * k, 0, 0, 0, E, F + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A E F
  · ring_nf; finish
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 3) E (F + 1))
    ring_nf; finish

theorem main_even (m : ℕ) :
    ⟨4 * m ^ 2 + 6 * m + 3, 0, 0, 0, 2 * m + 2, 2 * m + 2⟩ [fm]⊢⁺
    ⟨4 * m ^ 2 + 10 * m + 7, 0, 0, 0, 2 * m + 3, 2 * m + 3⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * m + 2) (4 * m ^ 2 + 6 * m + 3) 0 (2 * m + 2))
  rw [show 0 + (2 * m + 2) = 2 * m + 2 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨4 * m ^ 2 + 6 * m + 2, 1, 2 * m + 2, 0, 1, 2 * m + 2⟩)
  · rw [show 4 * m ^ 2 + 6 * m + 3 = (4 * m ^ 2 + 6 * m + 2) + 1 from by ring]; simp [fm]
  have hR1 : fm ⟨4 * m ^ 2 + 6 * m + 2, 1, 2 * m + 2, 0, 1, 2 * m + 2⟩ =
    some ⟨4 * m ^ 2 + 6 * m + 2, 0, 2 * m + 1, 1, 2, 2 * m + 2⟩ := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]; simp [fm]
  apply stepStar_trans (step_stepStar hR1)
  have hR3 : fm ⟨4 * m ^ 2 + 6 * m + 2, 0, 2 * m + 1, 1, 2, 2 * m + 2⟩ =
    some ⟨4 * m ^ 2 + 6 * m + 3, 2, 2 * m + 1, 0, 2, 2 * m + 1⟩ := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]; simp [fm]
  apply stepStar_trans (step_stepStar hR3)
  have heq : (4 * m ^ 2 + 6 * m + 3, 2, 2 * m + 1, 0, 2, 2 * m + 1) =
    (4 * m ^ 2 + 6 * m + 3, 2, 1 + 2 * m, 0, 2, (m + 1) + m) := by ring_nf
  rw [heq]
  apply stepStar_trans (inner_loop m (4 * m ^ 2 + 6 * m + 3) 1 0 2 (m + 1))
  rw [show 4 * m ^ 2 + 6 * m + 3 + m = 4 * m ^ 2 + 7 * m + 3 from by ring,
      show 0 + m = m from by ring,
      show 2 + 2 * m = 2 * m + 2 from by ring]
  apply stepStar_trans (even_remainder (4 * m ^ 2 + 7 * m + 3) m (2 * m + 2) m)
  rw [show 4 * m ^ 2 + 7 * m + 3 + 1 = 4 * m ^ 2 + 7 * m + 4 from by ring,
      show 2 * m + 2 + 1 = 2 * m + 3 from by ring,
      show m + 2 = (m + 1) + 1 from by ring]
  apply stepStar_trans (drain (m + 1) (4 * m ^ 2 + 7 * m + 4) (2 * m + 3) (m + 1))
  ring_nf; finish

theorem main_odd (m : ℕ) :
    ⟨4 * m ^ 2 + 10 * m + 7, 0, 0, 0, 2 * m + 3, 2 * m + 3⟩ [fm]⊢⁺
    ⟨4 * m ^ 2 + 14 * m + 13, 0, 0, 0, 2 * m + 4, 2 * m + 4⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * m + 3) (4 * m ^ 2 + 10 * m + 7) 0 (2 * m + 3))
  rw [show 0 + (2 * m + 3) = 2 * m + 3 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨4 * m ^ 2 + 10 * m + 6, 1, 2 * m + 3, 0, 1, 2 * m + 3⟩)
  · rw [show 4 * m ^ 2 + 10 * m + 7 = (4 * m ^ 2 + 10 * m + 6) + 1 from by ring]; simp [fm]
  have hR1 : fm ⟨4 * m ^ 2 + 10 * m + 6, 1, 2 * m + 3, 0, 1, 2 * m + 3⟩ =
    some ⟨4 * m ^ 2 + 10 * m + 6, 0, 2 * m + 2, 1, 2, 2 * m + 3⟩ := by
    rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]; simp [fm]
  apply stepStar_trans (step_stepStar hR1)
  have hR3 : fm ⟨4 * m ^ 2 + 10 * m + 6, 0, 2 * m + 2, 1, 2, 2 * m + 3⟩ =
    some ⟨4 * m ^ 2 + 10 * m + 7, 2, 2 * m + 2, 0, 2, 2 * m + 2⟩ := by
    rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]; simp [fm]
  apply stepStar_trans (step_stepStar hR3)
  have heq : (4 * m ^ 2 + 10 * m + 7, 2, 2 * m + 2, 0, 2, 2 * m + 2) =
    (4 * m ^ 2 + 10 * m + 7, 2, 0 + 2 * (m + 1), 0, 2, (m + 1) + (m + 1)) := by ring_nf
  rw [heq]
  apply stepStar_trans (inner_loop (m + 1) (4 * m ^ 2 + 10 * m + 7) 0 0 2 (m + 1))
  rw [show 4 * m ^ 2 + 10 * m + 7 + (m + 1) = 4 * m ^ 2 + 11 * m + 8 from by ring,
      show 0 + (m + 1) = m + 1 from by ring,
      show 2 + 2 * (m + 1) = 2 * m + 4 from by ring]
  apply stepStar_trans (odd_remainder (4 * m ^ 2 + 11 * m + 8) (m + 1) (2 * m + 4) (m + 1))
  rw [show 4 * m ^ 2 + 11 * m + 8 + 2 = 4 * m ^ 2 + 11 * m + 10 from by ring,
      show m + 1 + 2 = (m + 2) + 1 from by ring]
  apply stepStar_trans (drain (m + 1) (4 * m ^ 2 + 11 * m + 10) (2 * m + 4) (m + 2))
  ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n ^ 2 + 3 * n + 3, 0, 0, 0, n + 2, n + 2⟩ [fm]⊢⁺
    ⟨n ^ 2 + 5 * n + 7, 0, 0, 0, n + 3, n + 3⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rw [show (2 * m) ^ 2 + 3 * (2 * m) + 3 = 4 * m ^ 2 + 6 * m + 3 from by ring,
        show (2 * m) ^ 2 + 5 * (2 * m) + 7 = 4 * m ^ 2 + 10 * m + 7 from by ring,
        show 2 * m + 2 = 2 * m + 2 from rfl,
        show 2 * m + 3 = 2 * m + 3 from rfl]
    exact main_even m
  · subst hm
    rw [show (2 * m + 1) ^ 2 + 3 * (2 * m + 1) + 3 = 4 * m ^ 2 + 10 * m + 7 from by ring,
        show (2 * m + 1) ^ 2 + 5 * (2 * m + 1) + 7 = 4 * m ^ 2 + 14 * m + 13 from by ring,
        show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 2 * m + 1 + 3 = 2 * m + 4 from by ring]
    exact main_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 2, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n * n + 3 * n + 3, 0, 0, 0, n + 2, n + 2⟩) 0
  intro n; refine ⟨n + 1, ?_⟩
  rw [show (n + 1) * (n + 1) + 3 * (n + 1) + 3 = n ^ 2 + 5 * n + 7 from by ring,
      show n * n + 3 * n + 3 = n ^ 2 + 3 * n + 3 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1627
