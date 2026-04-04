import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1770: [9/10, 245/33, 4/3, 11/7, 21/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1  2 -1
 2 -1  0  0  0
 0  0  0 -1  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1770

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem d_to_e : ∀ k, ∀ e, ⟨a, 0, 0, k, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  · step fm
    apply stepStar_trans (ih _); ring_nf; finish

theorem b_to_a : ∀ k, ∀ a, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  · step fm
    apply stepStar_trans (ih _); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ B D, ⟨k, B + 1, 0, D, k⟩ [fm]⊢* ⟨0, B + k + 1, 0, D + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro B D
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

theorem spiral : ⟨a, 2, 0, 3, a⟩ [fm]⊢* ⟨2 * a + 4, 0, 0, 2 * a + 3, 0⟩ := by
  apply stepStar_trans (r2r1_chain a 1 3)
  show ⟨0, 1 + a + 1, 0, 3 + 2 * a, 0⟩ [fm]⊢* ⟨2 * a + 4, 0, 0, 2 * a + 3, 0⟩
  rw [show 1 + a + 1 = a + 2 from by ring,
      show 3 + 2 * a = 2 * a + 3 from by ring]
  apply stepStar_trans (b_to_a (a + 2) 0)
  show ⟨0 + 2 * (a + 2), 0, 0, 2 * a + 3, 0⟩ [fm]⊢* _
  ring_nf; finish

theorem opening : ⟨a + 2, 0, 0, 0, a + 1⟩ [fm]⊢⁺ ⟨a, 2, 0, 3, a⟩ := by
  step fm; step fm; step fm; finish

theorem main_trans : ∀ a, ⟨a + 1, 0, 0, a, 0⟩ [fm]⊢⁺ ⟨2 * a + 2, 0, 0, 2 * a + 1, 0⟩ := by
  intro a
  rcases a with _ | a
  · execute fm 2
  · show ⟨a + 2, 0, 0, a + 1, 0⟩ [fm]⊢⁺ ⟨2 * a + 4, 0, 0, 2 * a + 3, 0⟩
    apply stepStar_stepPlus_stepPlus
    · exact d_to_e (a + 1) 0
    · simp only [Nat.zero_add]
      apply stepPlus_stepStar_stepPlus (opening (a := a))
      exact spiral

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, n, 0⟩) 0
  intro n; exact ⟨2 * n + 1, main_trans n⟩
