import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #932: [4/15, 33/14, 25/2, 7/11, 231/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 0  1 -1  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_932

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    have := ih (a + 1) c d (e + 1)
    ring_nf at this ⊢; exact this

theorem r3_drain : ∀ j, ∀ c e,
    ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * j, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro c e
  · exists 0
  · step fm
    have := ih (c + 2) e
    ring_nf at this ⊢; exact this

theorem e_to_d : ∀ k, ∀ c d e,
    ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    have := ih c (d + 1) e
    ring_nf at this ⊢; exact this

theorem main_trans (k d : ℕ) :
    ⟨0, 0, k + d + 3, d, 0⟩ [fm]⊢⁺ ⟨0, 0, k + 2 * d + 6, d + 2, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, k + d + 3, d, 0⟩ = some ⟨0, 1, k + d + 2, d + 1, 1⟩
    unfold fm; simp only
  have h1 : ⟨0, 1, k + d + 2, d + 1, 1⟩ [fm]⊢* ⟨2, 0, k + d + 1, d + 1, 1⟩ := by
    step fm; finish
  have h2 : ⟨2, 0, k + d + 1, d + 1, 1⟩ [fm]⊢*
      ⟨d + 3, 0, k, 0, d + 2⟩ := by
    have := r2r1_chain (d + 1) 1 k 0 1
    ring_nf at this ⊢; exact this
  have h3 : ⟨d + 3, 0, k, 0, d + 2⟩ [fm]⊢*
      ⟨0, 0, k + 2 * d + 6, 0, d + 2⟩ := by
    have := r3_drain (d + 3) k (d + 2)
    ring_nf at this ⊢; exact this
  have h4 : ⟨0, 0, k + 2 * d + 6, 0, d + 2⟩ [fm]⊢*
      ⟨0, 0, k + 2 * d + 6, d + 2, 0⟩ := by
    have := e_to_d (d + 2) (k + 2 * d + 6) 0 0
    ring_nf at this ⊢; exact this
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 2, 0⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, p.1 + p.2 + 3, p.2, 0⟩) ⟨0, 2⟩
  intro ⟨k, d⟩
  refine ⟨⟨k + d + 1, d + 2⟩, ?_⟩
  show ⟨0, 0, k + d + 3, d, 0⟩ [fm]⊢⁺
    ⟨0, 0, (k + d + 1) + (d + 2) + 3, d + 2, 0⟩
  rw [show (k + d + 1) + (d + 2) + 3 = k + 2 * d + 6 from by ring]
  exact main_trans k d

end Sz22_2003_unofficial_932
