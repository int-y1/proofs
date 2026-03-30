import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1038: [45/2, 22/35, 1/5, 49/3, 1/77, 5/7]

Vector representation:
```
-1  2  1  0  0
 1  0 -1 -1  1
 0  0 -1  0  0
 0 -1  0  2  0
 0  0  0 -1 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1038

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm
    apply stepStar_trans (ih b (d + 2) e)
    ring_nf; finish

theorem r5_chain : ∀ k, ∀ d,
    ⟨(0 : ℕ), 0, 0, d + k, k⟩ [fm]⊢* ⟨0, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih d)
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b, 1, d + k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 2) d (e + 1))
    ring_nf; finish

theorem main_trans (k : ℕ) (hk : k ≥ 1) :
    ⟨(0 : ℕ), 2 * k, 0, 0, k⟩ [fm]⊢⁺ ⟨0, 2 * (3 * k - 1), 0, 0, 3 * k - 1⟩ := by
  have h1 : ⟨(0 : ℕ), 2 * k, 0, 0, k⟩ [fm]⊢* ⟨0, 0, 0, 4 * k, k⟩ := by
    have := r4_chain (2 * k) 0 0 k
    convert this using 1; ring_nf
  have h2 : ⟨(0 : ℕ), 0, 0, 4 * k, k⟩ [fm]⊢* ⟨0, 0, 0, 3 * k, 0⟩ := by
    have := r5_chain k (3 * k)
    convert this using 1; ring_nf
  have h3 : ⟨(0 : ℕ), 0, 0, 3 * k, 0⟩ [fm]⊢⁺ ⟨0, 0, 1, 3 * k - 1, 0⟩ := by
    rw [show 3 * k = (3 * k - 1) + 1 from by omega]
    step fm; finish
  have h4 : ⟨(0 : ℕ), 0, 1, 3 * k - 1, 0⟩ [fm]⊢* ⟨0, 2 * (3 * k - 1), 1, 0, 3 * k - 1⟩ := by
    have := r2r1_chain (3 * k - 1) 0 0 0
    simp at this; exact this
  have h5 : ⟨(0 : ℕ), 2 * (3 * k - 1), 1, 0, 3 * k - 1⟩ [fm]⊢⁺
      ⟨0, 2 * (3 * k - 1), 0, 0, 3 * k - 1⟩ := by
    step fm; finish
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus
        (stepPlus_stepStar_stepPlus h3 h4) (stepPlus_stepStar h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 6, 0, 0, 3⟩) (by execute fm 12)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k, q = ⟨0, 2 * k, 0, 0, k⟩ ∧ k ≥ 1)
  · intro c ⟨k, hc, hk⟩
    subst hc
    exact ⟨⟨0, 2 * (3 * k - 1), 0, 0, 3 * k - 1⟩,
      ⟨3 * k - 1, rfl, by omega⟩, main_trans k hk⟩
  · exact ⟨3, rfl, by omega⟩
