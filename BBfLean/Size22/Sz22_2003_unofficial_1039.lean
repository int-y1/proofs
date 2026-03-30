import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1039: [45/2, 4/105, 11/5, 49/33, 5/7]

Vector representation:
```
-1  2  1  0  0
 2 -1 -1 -1  0
 0  0 -1  0  1
 0 -1  0  2 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1039

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d,
    ⟨(0 : ℕ), b + k, 0, d, k⟩ [fm]⊢* ⟨0, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm
    apply stepStar_trans (ih b (d + 2))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ b e,
    ⟨(0 : ℕ), b, k, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih b (e + 1))
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ B C,
    ⟨(0 : ℕ), B + 1, C + 1, k, 0⟩ [fm]⊢* ⟨0, B + 3 * k + 1, C + k + 1, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro B C
  · ring_nf; finish
  · rw [show B + 3 * (k + 1) + 1 = (B + 3) + 3 * k + 1 from by ring,
        show C + (k + 1) + 1 = (C + 1) + k + 1 from by ring]
    step fm; step fm; step fm
    rw [show B + 2 + 2 = (B + 3) + 1 from by ring,
        show C + 1 + 1 = (C + 1) + 1 from by ring]
    apply stepStar_trans (ih (B + 3) (C + 1))
    ring_nf; finish

theorem main_trans (s e : ℕ) :
    ⟨(0 : ℕ), s + e + 2, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨0, s + 6 * e + 4, 0, 0, 2 * e + 2⟩ := by
  have h1 : ⟨(0 : ℕ), s + e + 2, 0, 0, e + 1⟩ [fm]⊢*
      ⟨0, s + 1, 0, 2 * e + 2, 0⟩ := by
    have := r4_chain (e + 1) (s + 1) 0
    rw [show s + 1 + (e + 1) = s + e + 2 from by ring,
        show 0 + 2 * (e + 1) = 2 * e + 2 from by ring] at this
    exact this
  have h2 : ⟨(0 : ℕ), s + 1, 0, 2 * e + 2, 0⟩ [fm]⊢⁺
      ⟨0, s + 1, 1, 2 * e + 1, 0⟩ := by
    rw [show 2 * e + 2 = (2 * e + 1) + 1 from by ring]
    step fm; finish
  have h3 : ⟨(0 : ℕ), s + 1, 1, 2 * e + 1, 0⟩ [fm]⊢*
      ⟨0, s + 6 * e + 4, 2 * e + 2, 0, 0⟩ := by
    have := r2r1r1_chain (2 * e + 1) s 0
    rw [show s + 1 = s + 1 from rfl,
        show (0 : ℕ) + 1 = 1 from by ring,
        show s + 3 * (2 * e + 1) + 1 = s + 6 * e + 4 from by ring,
        show 0 + (2 * e + 1) + 1 = 2 * e + 2 from by ring] at this
    exact this
  have h4 : ⟨(0 : ℕ), s + 6 * e + 4, 2 * e + 2, 0, 0⟩ [fm]⊢*
      ⟨0, s + 6 * e + 4, 0, 0, 2 * e + 2⟩ := by
    have := r3_chain (2 * e + 2) (s + 6 * e + 4) 0
    rw [show (0 : ℕ) + (2 * e + 2) = 2 * e + 2 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨s, e⟩ ↦ ⟨0, s + e + 2, 0, 0, e + 1⟩) ⟨0, 0⟩
  intro ⟨s, e⟩
  refine ⟨⟨s + 4 * e + 1, 2 * e + 1⟩, ?_⟩
  show ⟨(0 : ℕ), s + e + 2, 0, 0, e + 1⟩ [fm]⊢⁺
      ⟨0, (s + 4 * e + 1) + (2 * e + 1) + 2, 0, 0, (2 * e + 1) + 1⟩
  have h := main_trans s e
  rw [show (s + 4 * e + 1) + (2 * e + 1) + 2 = s + 6 * e + 4 from by ring,
      show (2 * e + 1) + 1 = 2 * e + 2 from by ring]
  exact h

end Sz22_2003_unofficial_1039
