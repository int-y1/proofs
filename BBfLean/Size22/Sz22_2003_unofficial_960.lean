import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #960: [4/15, 33/14, 325/2, 7/11, 33/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  2  0  0  1
 0  0  0  1 -1  0
 0  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_960

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

theorem r1r2_chain : ∀ k, ∀ a c e g,
    ⟨a, 1, c + k + 1, k, e, g⟩ [fm]⊢* ⟨a + k, 1, c + 1, 0, e + k, g⟩ := by
  intro k; induction' k with k ih <;> intro a c e g
  · ring_nf; finish
  · rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1) g); ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e g,
    ⟨k, 0, c, 0, e, g⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e, g + k⟩ := by
  intro k; induction' k with k ih <;> intro c e g
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) e (g + 1)); ring_nf; finish

theorem r4_drain : ∀ k, ∀ c d g,
    ⟨0, 0, c, d, k, g⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, g⟩ := by
  intro k; induction' k with k ih <;> intro c d g
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1) g); ring_nf; finish

theorem main_trans (c d g : ℕ) :
    ⟨0, 0, c + d + 2, d, 0, g + 1⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * d + 5, d + 1, 0, g + d + 2⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, c + d + 2, d, 0, g + 1⟩ = some ⟨0, 1, c + d + 2, d, 1, g⟩
    unfold fm; simp only
  have h2 : ⟨0, 1, c + d + 2, d, 1, g⟩ [fm]⊢*
      ⟨d, 1, c + 2, 0, d + 1, g⟩ := by
    have := r1r2_chain d 0 (c + 1) 1 g
    rw [show (c + 1) + d + 1 = c + d + 2 from by ring,
        show 0 + d = d from by ring,
        show 1 + d = d + 1 from by ring,
        show (c + 1) + 1 = c + 2 from by ring] at this
    exact this
  have h3 : ⟨d, 1, c + 2, 0, d + 1, g⟩ [fm]⊢*
      ⟨d + 2, 0, c + 1, 0, d + 1, g⟩ := by
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply step_stepStar
    show fm ⟨d, 1, (c + 1) + 1, 0, d + 1, g⟩ = some ⟨d + 2, 0, c + 1, 0, d + 1, g⟩
    unfold fm; simp only
  have h4 : ⟨d + 2, 0, c + 1, 0, d + 1, g⟩ [fm]⊢*
      ⟨0, 0, c + 2 * d + 5, 0, d + 1, g + d + 2⟩ := by
    have := r3_drain (d + 2) (c + 1) (d + 1) g
    rw [show (c + 1) + 2 * (d + 2) = c + 2 * d + 5 from by ring,
        show g + (d + 2) = g + d + 2 from by ring] at this
    exact this
  have h5 : ⟨0, 0, c + 2 * d + 5, 0, d + 1, g + d + 2⟩ [fm]⊢*
      ⟨0, 0, c + 2 * d + 5, d + 1, 0, g + d + 2⟩ := by
    have := r4_drain (d + 1) (c + 2 * d + 5) 0 (g + d + 2)
    rw [show 0 + (d + 1) = d + 1 from by ring] at this
    exact this
  exact stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨c, d, g⟩ ↦ ⟨0, 0, c + d + 2, d, 0, g + 1⟩) ⟨0, 0, 0⟩
  intro ⟨c, d, g⟩
  refine ⟨⟨c + d + 2, d + 1, g + d + 1⟩, ?_⟩
  show ⟨0, 0, c + d + 2, d, 0, g + 1⟩ [fm]⊢⁺
    ⟨0, 0, (c + d + 2) + (d + 1) + 2, d + 1, 0, (g + d + 1) + 1⟩
  rw [show (c + d + 2) + (d + 1) + 2 = c + 2 * d + 5 from by ring,
      show (g + d + 1) + 1 = g + d + 2 from by ring]
  exact main_trans c d g

end Sz22_2003_unofficial_960
