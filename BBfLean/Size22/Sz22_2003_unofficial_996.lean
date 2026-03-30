import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #996: [4/15, 33/14, 845/2, 7/11, 21/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  2
 0  0  0  1 -1  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_996

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+2⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ c e f,
    ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 1) e (f + 2)); ring_nf; finish

theorem r4_drain : ∀ k, ∀ c d f,
    ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1) f); ring_nf; finish

theorem r1r2_chain : ∀ k, ∀ a c d e f,
    ⟨a, 1, c + k, d + k, e, f⟩ [fm]⊢* ⟨a + k, 1, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f); ring_nf; finish

theorem main_trans (a f : ℕ) :
    ⟨a + 2, 0, 0, 0, a + 1, f⟩ [fm]⊢⁺
    ⟨a + 3, 0, 0, 0, a + 2, f + 2 * a + 5⟩ := by
  have h1 : ⟨a + 2, 0, 0, 0, a + 1, f⟩ [fm]⊢*
      ⟨0, 0, a + 2, 0, a + 1, f + 2 * (a + 2)⟩ := by
    have := r3_drain (a + 2) 0 (a + 1) f
    rw [show 0 + (a + 2) = a + 2 from by ring] at this
    exact this
  have h2 : ⟨0, 0, a + 2, 0, a + 1, f + 2 * (a + 2)⟩ [fm]⊢*
      ⟨0, 0, a + 2, a + 1, 0, f + 2 * (a + 2)⟩ := by
    have := r4_drain (a + 1) (a + 2) 0 (f + 2 * (a + 2))
    rw [show 0 + (a + 1) = a + 1 from by ring] at this
    exact this
  have h3 : ⟨0, 0, a + 2, a + 1, 0, f + 2 * (a + 2)⟩ [fm]⊢⁺
      ⟨0, 1, a + 2, a + 2, 0, f + 2 * (a + 2) - 1⟩ := by
    rw [show f + 2 * (a + 2) = (f + 2 * (a + 2) - 1) + 1 from by omega]
    apply step_stepPlus
    show fm ⟨0, 0, a + 2, a + 1, 0, (f + 2 * (a + 2) - 1) + 1⟩ =
      some ⟨0, 0 + 1, a + 2, a + 1 + 1, 0, f + 2 * (a + 2) - 1⟩
    unfold fm; simp only
  have h4 : ⟨0, 1, a + 2, a + 2, 0, f + 2 * (a + 2) - 1⟩ [fm]⊢*
      ⟨a + 2, 1, 0, 0, a + 2, f + 2 * (a + 2) - 1⟩ := by
    have := r1r2_chain (a + 2) 0 0 0 0 (f + 2 * (a + 2) - 1)
    simp only [Nat.zero_add] at this
    exact this
  have h5 : ⟨a + 2, 1, 0, 0, a + 2, f + 2 * (a + 2) - 1⟩ [fm]⊢*
      ⟨a + 3, 0, 0, 0, a + 2, f + 2 * a + 5⟩ := by
    rw [show a + 2 = (a + 1) + 1 from by ring]
    step fm; step fm
    rw [show f + 2 * (a + 2) - 1 + 2 = f + 2 * a + 5 from by omega]
    finish
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h3
        (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1, 3⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, f⟩ ↦ ⟨a + 2, 0, 0, 0, a + 1, f⟩) ⟨0, 3⟩
  intro ⟨a, f⟩
  refine ⟨⟨a + 1, f + 2 * a + 5⟩, ?_⟩
  show ⟨a + 2, 0, 0, 0, a + 1, f⟩ [fm]⊢⁺
    ⟨(a + 1) + 2, 0, 0, 0, (a + 1) + 1, f + 2 * a + 5⟩
  rw [show (a + 1) + 2 = a + 3 from by ring,
      show (a + 1) + 1 = a + 2 from by ring]
  exact main_trans a f
