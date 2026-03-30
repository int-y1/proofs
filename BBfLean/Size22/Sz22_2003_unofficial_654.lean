import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #654: [35/6, 1573/2, 28/55, 3/7, 5/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  2  1
 2  0 -1  1 -1  0
 0  1  0 -1  0  0
 0  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_654

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R4 chain: move d to b
theorem d_to_b : ∀ k b d e f, ⟨(0 : ℕ), b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (b + 1) d e f); ring_nf; finish

-- R3R1R1 chain
theorem r3r1r1_chain : ∀ k b c d e f,
    ⟨(0 : ℕ), 2 * k + b, c + 1, d, e + k, f⟩ [fm]⊢*
    ⟨0, b, c + k + 1, d + 3 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · ring_nf; exists 0
  · rw [show 2 * (k + 1) + b = (2 * k + b) + 2 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 3) e f)
    ring_nf; finish

-- R3R1R2 partial step
theorem r3r1r2_step : ∀ c d e f,
    ⟨(0 : ℕ), 1, c + 1, d, e + 1, f⟩ [fm]⊢* ⟨0, 0, c + 1, d + 2, e + 2, f + 1⟩ := by
  intro c d e f; step fm; step fm; step fm; finish

-- R3R2R2 chain
theorem r3r2r2_chain : ∀ k c d e f,
    ⟨(0 : ℕ), 0, c + k, d, e + 1, f⟩ [fm]⊢*
    ⟨0, 0, c, d + k, e + 3 * k + 1, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · ring_nf; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 2 + 2 = (e + 3) + 1 from by ring,
        show f + 1 + 1 = f + 2 from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 3) (f + 2))
    ring_nf; finish

-- Even case
theorem main_even (k g : ℕ) (hg : g ≥ 1) :
    ⟨(0 : ℕ), 0, 0, 2 * k, 2 * k + g, 2 * k + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * k + 1, 4 * k + g + 3, 4 * k + 2⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 0, 2 * k, 2 * k + g, 2 * k + 1⟩ [fm]⊢*
      ⟨0, 2 * k, 0, 0, 2 * k + g, 2 * k + 1⟩ := by
    have := d_to_b (2 * k) 0 0 (2 * k + g) (2 * k + 1); simp at this; exact this
  have h2 : ⟨(0 : ℕ), 2 * k, 0, 0, 2 * k + g, 2 * k + 1⟩ [fm]⊢
      ⟨0, 2 * k, 1, 0, 2 * k + g, 2 * k⟩ := by simp [fm]
  have h3 : ⟨(0 : ℕ), 2 * k, 1, 0, 2 * k + g, 2 * k⟩ [fm]⊢*
      ⟨0, 0, k + 1, 3 * k, k + g, 2 * k⟩ := by
    have := r3r1r1_chain k 0 0 0 (k + g) (2 * k); simp at this
    rw [show 2 * k + g = (k + g) + k from by ring]; exact this
  have h4 : ⟨(0 : ℕ), 0, k + 1, 3 * k, k + g, 2 * k⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * k + 1, 4 * k + g + 3, 4 * k + 2⟩ := by
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    rw [show k + (g' + 1) = (k + g') + 1 from by ring]
    have := r3r2r2_chain (k + 1) 0 (3 * k) (k + g') (2 * k); simp at this
    apply stepStar_trans this
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2 (stepStar_trans h3 h4))

-- Odd case
theorem main_odd (k g : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * k + 1, 2 * k + 1 + g, 2 * k + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * k + 3, 4 * k + g + 5, 4 * k + 4⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 0, 2 * k + 1, 2 * k + 1 + g, 2 * k + 2⟩ [fm]⊢*
      ⟨0, 2 * k + 1, 0, 0, 2 * k + 1 + g, 2 * k + 2⟩ := by
    have := d_to_b (2 * k + 1) 0 0 (2 * k + 1 + g) (2 * k + 2); simp at this; exact this
  have h2 : ⟨(0 : ℕ), 2 * k + 1, 0, 0, 2 * k + 1 + g, 2 * k + 2⟩ [fm]⊢
      ⟨0, 2 * k + 1, 1, 0, 2 * k + 1 + g, 2 * k + 1⟩ := by simp [fm]
  have h3 : ⟨(0 : ℕ), 2 * k + 1, 1, 0, 2 * k + 1 + g, 2 * k + 1⟩ [fm]⊢*
      ⟨0, 1, k + 1, 3 * k, k + 1 + g, 2 * k + 1⟩ := by
    have := r3r1r1_chain k 1 0 0 (k + 1 + g) (2 * k + 1); simp at this
    rw [show 2 * k + 1 + g = (k + 1 + g) + k from by ring]; exact this
  have h4 : ⟨(0 : ℕ), 1, k + 1, 3 * k, k + 1 + g, 2 * k + 1⟩ [fm]⊢*
      ⟨0, 0, k + 1, 3 * k + 2, k + g + 2, 2 * k + 2⟩ := by
    rw [show k + 1 + g = (k + g) + 1 from by ring]
    have := r3r1r2_step k (3 * k) (k + g) (2 * k + 1)
    convert this using 3
  have h5 : ⟨(0 : ℕ), 0, k + 1, 3 * k + 2, k + g + 2, 2 * k + 2⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * k + 3, 4 * k + g + 5, 4 * k + 4⟩ := by
    rw [show k + g + 2 = (k + g + 1) + 1 from by ring]
    have := r3r2r2_chain (k + 1) 0 (3 * k + 2) (k + g + 1) (2 * k + 2); simp at this
    apply stepStar_trans this
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d g, q = ⟨0, 0, 0, d, d + g, d + 1⟩ ∧ g ≥ 2)
  · intro c ⟨d, g, hq, hg⟩; subst hq
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [show k + k = 2 * k from by ring] at hk; subst hk
      refine ⟨⟨0, 0, 0, 4 * k + 1, 4 * k + 1 + (g + 2), 4 * k + 1 + 1⟩,
        ⟨4 * k + 1, g + 2, ?_, by omega⟩, ?_⟩
      · rfl
      · rw [show 4 * k + 1 + (g + 2) = 4 * k + g + 3 from by ring,
             show 4 * k + 1 + 1 = 4 * k + 2 from by ring]
        exact main_even k g (by omega)
    · subst hk
      refine ⟨⟨0, 0, 0, 4 * k + 3, 4 * k + 3 + (g + 2), 4 * k + 3 + 1⟩,
        ⟨4 * k + 3, g + 2, ?_, by omega⟩, ?_⟩
      · rfl
      · rw [show 4 * k + 3 + (g + 2) = 4 * k + g + 5 from by ring,
             show 4 * k + 3 + 1 = 4 * k + 4 from by ring,
             show 2 * k + 1 + 1 = 2 * k + 2 from by ring]
        exact main_odd k g
  · exact ⟨0, 2, rfl, by omega⟩

end Sz22_2003_unofficial_654
