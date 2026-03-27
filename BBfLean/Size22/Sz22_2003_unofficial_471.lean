import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #471: [28/15, 21/22, 25/2, 11/7, 6/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  1 -1
-1  0  2  0  0
 0  0  0 -1  1
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_471

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

theorem d_to_e : ∀ k, ∀ c d e, (⟨0, 0, c, d + k, e⟩ : Q) [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  rw [show e + (k + 1) = (e + 1) + k from by ring]
  exact h _ _ _

theorem a_to_c : ∀ k, ∀ c d, (⟨k, 0, c, d, 0⟩ : Q) [fm]⊢* ⟨0, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  step fm
  rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
  exact h _ _

theorem r2r1_chain : ∀ k, ∀ a c d,
    (⟨a + 1, 0, c + k + 1, d, k + 1⟩ : Q) [fm]⊢* ⟨a + k + 2, 0, c, d + 2 * k + 2, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · step fm; step fm; ring_nf; finish
  rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring,
      show (k + 1) + 1 = (k + 1) + 1 from rfl]
  step fm; step fm
  rw [show a + (k + 1) + 2 = (a + 1) + k + 2 from by ring,
      show d + 2 * (k + 1) + 2 = (d + 2) + 2 * k + 2 from by ring]
  exact h _ _ _

theorem main_trans (c d : ℕ) :
    (⟨0, 0, c + d + 3, d + 1, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, c + 2 * d + 8, 2 * d + 3, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, c + d + 3, 0, d + 1⟩)
  · have h := d_to_e (d + 1) (c + d + 3) 0 0
    simp only [Nat.zero_add] at h; exact h
  step fm; step fm
  apply stepStar_trans (c₂ := ⟨d + 4, 0, c, 2 * d + 3, 0⟩)
  · have h := r2r1_chain d 2 c 1
    rw [show 2 + d + 2 = d + 4 from by ring,
        show 1 + 2 * d + 2 = 2 * d + 3 from by ring] at h
    convert h using 2
  · have h := a_to_c (d + 4) c (2 * d + 3)
    rw [show c + 2 * (d + 4) = c + 2 * d + 8 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 6, 1, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c + d + 3, d + 1, 0⟩)
  · intro q ⟨c, d, hq⟩
    subst hq
    exact ⟨⟨0, 0, (c + 3) + (2 * d + 2) + 3, (2 * d + 2) + 1, 0⟩,
           ⟨c + 3, 2 * d + 2, rfl⟩,
           by rw [show (c + 3) + (2 * d + 2) + 3 = c + 2 * d + 8 from by ring,
                  show (2 * d + 2) + 1 = 2 * d + 3 from by ring]
              exact main_trans c d⟩
  · exact ⟨3, 0, rfl⟩

end Sz22_2003_unofficial_471
