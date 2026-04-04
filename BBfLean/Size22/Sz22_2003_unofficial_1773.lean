import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1773: [9/10, 275/21, 2/3, 7/11, 99/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  2 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1773

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem b_to_a : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

theorem interleaved : ∀ d, ∀ a b e, ⟨a + 2 * d, b + 1, 0, d, e⟩ [fm]⊢*
    ⟨a, b + 3 * d + 1, 0, 0, e + d⟩ := by
  intro d; induction' d with d ih <;> intro a b e
  · exists 0
  · rw [show a + 2 * (d + 1) = (a + 2 * d) + 2 from by ring,
        show (d : ℕ) + 1 = d + 1 from rfl]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih a (b + 3) (e + 1))
    ring_nf; finish

theorem main_phase : ⟨a + 2 * d, 2, 0, d, 1⟩ [fm]⊢* ⟨a + 3 * d + 2, 0, 0, d + 1, 0⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (interleaved d a 1 1)
  rw [show 1 + 3 * d + 1 = 0 + (3 * d + 2) from by ring,
      show 1 + d = 0 + (d + 1) from by ring]
  apply stepStar_trans (b_to_a (3 * d + 2) (a := a) (b := 0) (e := 0 + (d + 1)))
  apply stepStar_trans (e_to_d (d + 1) (a := a + (3 * d + 2)) (d := 0) (e := 0))
  ring_nf; finish

theorem main_trans : ⟨a + 2 * d + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 3 * d + 2, 0, 0, d + 1, 0⟩ := by
  step fm
  exact main_phase

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 3, 0⟩)
  · execute fm 33
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ a ≥ 2 * d + 1)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * d + 1 := ⟨a - (2 * d + 1), by omega⟩
    refine ⟨⟨F + 3 * d + 2, 0, 0, d + 1, 0⟩,
      ⟨F + 3 * d + 2, d + 1, rfl, by omega, by omega⟩, main_trans⟩
  · exact ⟨7, 3, rfl, by omega, by omega⟩
