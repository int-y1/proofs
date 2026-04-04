import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1772: [9/10, 275/21, 2/3, 7/11, 63/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  2 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1772

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

theorem e_to_d : ∀ k, ∀ d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih
  · intro d; exists 0
  · intro d
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

theorem b_to_a : ∀ k, ∀ a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a e; exists 0
  · intro a e
    step fm
    apply stepStar_trans (ih (a + 1) e)
    ring_nf; finish

theorem interleaved_chain : ∀ k, ∀ a b d e,
    ⟨a + 2 * k, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨a, b + 3 * k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a b d e; exists 0
  · intro a b d e
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show b + 1 + 3 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih a (b + 3) d (e + 1))
    ring_nf; finish

theorem main_trans (a e : ℕ) : ⟨a + 2 * e + 5, 0, 0, 0, e + 1⟩ [fm]⊢⁺
    ⟨a + 3 * e + 8, 0, 0, 0, e + 2⟩ := by
  have h1 : ⟨a + 2 * e + 5, 0, 0, 0, e + 1⟩ [fm]⊢* ⟨a + 2 * e + 5, 0, 0, e + 1, 0⟩ := by
    rw [show (e + 1 : ℕ) = 0 + (e + 1) from by ring]
    exact e_to_d (e + 1) 0
  have h2 : ⟨a + 2 * e + 5, 0, 0, e + 1, 0⟩ [fm]⊢ ⟨a + 2 * e + 4, 2, 0, e + 2, 0⟩ := by
    show ((a + 2 * e + 4) + 1, 0, 0, e + 1, 0) [fm]⊢ _
    simp [fm]
  have h3 : ⟨a + 2 * e + 4, 2, 0, e + 2, 0⟩ [fm]⊢* ⟨a, 3 * e + 8, 0, 0, e + 2⟩ := by
    have := interleaved_chain (e + 2) a 1 0 0
    rw [show a + 2 * (e + 2) = a + 2 * e + 4 from by ring,
        show (1 : ℕ) + 1 = 2 from by ring,
        show 0 + (e + 2) = e + 2 from by ring,
        show 1 + 3 * (e + 2) + 1 = 3 * e + 8 from by ring] at this
    exact this
  have h4 : ⟨a, 3 * e + 8, 0, 0, e + 2⟩ [fm]⊢* ⟨a + 3 * e + 8, 0, 0, 0, e + 2⟩ := by
    exact b_to_a (3 * e + 8) a (e + 2)
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨15, 0, 0, 0, 4⟩) (by execute fm 78)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + 2 * e + 5, 0, 0, 0, e + 1⟩) ⟨4, 3⟩
  intro ⟨a, e⟩
  refine ⟨⟨a + e + 1, e + 1⟩, ?_⟩
  show ⟨a + 2 * e + 5, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨(a + e + 1) + 2 * (e + 1) + 5, 0, 0, 0, (e + 1) + 1⟩
  rw [show (a + e + 1) + 2 * (e + 1) + 5 = a + 3 * e + 8 from by ring,
      show (e + 1) + 1 = e + 2 from by ring]
  exact main_trans a e
