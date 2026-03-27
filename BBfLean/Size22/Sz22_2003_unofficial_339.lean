import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #339: [189/10, 35/33, 2/3, 11/7, 15/2]

Vector representation:
```
-1  3 -1  1  0
 0 -1  1  1 -1
 1 -1  0  0  0
 0  0  0 -1  1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_339

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem d_to_e : ∀ k a e, ⟨a, 0, 0, k + 1, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; ring_nf; finish
  · step fm
    apply stepStar_trans (ih a (e + 1))
    rw [show e + 1 + k + 1 = e + (k + 1) + 1 from by ring]; finish

theorem r2r1_loop : ∀ k a b d,
    ⟨a + k, b + 1, 0, d, k⟩ [fm]⊢* ⟨a, b + 2 * k + 1, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · simp [show 2 * 0 = 0 from rfl]; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    rw [show b + 1 + 2 = (b + 2) + 1 from by ring,
        show d + 1 + 1 = d + 2 from by ring]
    apply stepStar_trans (ih a (b + 2) (d + 2))
    rw [show b + 2 + 2 * k + 1 = b + 2 * (k + 1) + 1 from by ring,
        show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]
    finish

theorem b_to_a : ∀ k a d, ⟨a, k + 1, 0, d, 0⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 1) d)
    rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by ring]; finish

theorem main_cycle : ∀ a d, ⟨a + d + 3, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 6, 0, 0, 2 * d + 3, 0⟩ := by
  intro a d
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + d + 3, 0, 0, 0, d + 1⟩)
  · have h := d_to_e d (a + d + 3) 0
    rw [show 0 + d + 1 = d + 1 from by ring] at h; exact h
  step fm; step fm; step fm; step fm
  apply stepStar_trans (c₂ := ⟨a, 2 * d + 6, 0, 2 * d + 3, 0⟩)
  · have h := r2r1_loop d a 5 3
    rw [show 5 + 2 * d + 1 = 2 * d + 6 from by ring,
        show 3 + 2 * d = 2 * d + 3 from by ring] at h
    exact h
  step fm
  have h := b_to_a (2 * d + 4) (a + 1) (2 * d + 3)
  rw [show a + 1 + (2 * d + 4) + 1 = a + 2 * d + 6 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = (⟨a + d + 3, 0, 0, d + 1, 0⟩ : Q))
  · intro q ⟨a, d, hq⟩; subst hq
    exact ⟨⟨a + 2 * d + 6, 0, 0, 2 * d + 3, 0⟩,
           ⟨a + 1, 2 * d + 2, by ring_nf⟩,
           main_cycle a d⟩
  · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_339
