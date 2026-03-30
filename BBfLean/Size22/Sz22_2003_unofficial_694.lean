import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #694: [35/6, 4/55, 11/2, 3/7, 84/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 2  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_694

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ b c d, ⟨2, b + 2 * k, c, d, k⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2))
    ring_nf; finish

theorem r3r2_drain : ∀ k, ∀ a d, ⟨a + 1, 0, k + 1, d, 0⟩ [fm]⊢* ⟨a + k + 2, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; finish
  · rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) d)
    ring_nf; finish

theorem main_trans (k : ℕ) :
    ⟨0, 2 * k, 0, 0, k + 1⟩ [fm]⊢⁺ ⟨0, 2 * k + 2, 0, 0, k + 2⟩ := by
  rw [show k + 1 = k + 1 from rfl]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * k, 0, 0, k + 1⟩ = some ⟨2, 2 * k + 1, 0, 1, k⟩
    simp [fm]
  rw [show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans (r1r1r2_chain k 1 0 1)
  rw [show 0 + k = k from by ring,
      show 1 + 2 * k = 2 * k + 1 from by ring]
  apply stepStar_trans
  · show ⟨2, 1, k, 2 * k + 1, 0⟩ [fm]⊢* ⟨1, 0, k + 1, 2 * k + 2, 0⟩
    step fm; finish
  apply stepStar_trans (r3r2_drain k 0 (2 * k + 2))
  rw [show 0 + k + 2 = k + 2 from by ring]
  have h1 := r3_chain (k + 2) 0 (2 * k + 2) 0
  simp at h1
  apply stepStar_trans h1
  have h2 := r4_chain (2 * k + 2) 0 0 (k + 2)
  simp at h2
  exact h2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 2⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2 * (n + 1), 0, 0, n + 2⟩) 0
  intro n; exact ⟨n + 1, main_trans (n + 1)⟩

end Sz22_2003_unofficial_694
