import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1020: [4/15, 99/14, 275/2, 7/11, 3/5]

Vector representation:
```
 2 -1 -1  0  0
-1  2  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1020

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ c d,
    ⟨(0 : ℕ), 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a c e,
    ⟨a + k, (0 : ℕ), c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) (e + 1))
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, (0 : ℕ), c + 2 * k, d + k, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show a + 3 * (k + 1) + 1 = (a + 3) + 3 * k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) c d (e + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a b d e,
    ⟨a + k, b, (0 : ℕ), d + k, e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2) d (e + 1))
    ring_nf; finish

theorem r3r1r1_chain : ∀ k, ∀ a b e,
    ⟨a + 1, b + 2 * k, (0 : ℕ), 0, e⟩ [fm]⊢* ⟨a + 3 * k + 1, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show a + 3 * (k + 1) + 1 = (a + 3) + 3 * k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) b (e + 1))
    ring_nf; finish

theorem main_trans (a e : ℕ) :
    ⟨a + e + 2, (0 : ℕ), 0, 0, e⟩ [fm]⊢⁺
    ⟨3 * a + 5 * e + 7, 0, 0, 0, a + 3 * e + 3⟩ := by
  have h1 : ⟨a + e + 2, (0 : ℕ), 0, 0, e⟩ [fm]⊢*
      ⟨0, 0, 2 * a + 2 * e + 4, 0, a + 2 * e + 2⟩ := by
    rw [show a + e + 2 = 0 + (a + e + 2) from by ring]
    have := r3_chain (a + e + 2) 0 0 e
    rw [show (0 : ℕ) + 2 * (a + e + 2) = 2 * a + 2 * e + 4 from by ring,
        show e + (a + e + 2) = a + 2 * e + 2 from by ring] at this; exact this
  have h2 : ⟨(0 : ℕ), 0, 2 * a + 2 * e + 4, 0, a + 2 * e + 2⟩ [fm]⊢*
      ⟨0, 0, 2 * a + 2 * e + 4, a + 2 * e + 2, 0⟩ := by
    have := r4_chain (a + 2 * e + 2) (2 * a + 2 * e + 4) 0
    rw [show (0 : ℕ) + (a + 2 * e + 2) = a + 2 * e + 2 from by ring] at this; exact this
  have h3 : ⟨(0 : ℕ), 0, 2 * a + 2 * e + 4, a + 2 * e + 2, 0⟩ [fm]⊢⁺
      ⟨2, 0, 2 * a + 2 * e + 2, a + 2 * e + 2, 0⟩ := by
    rw [show 2 * a + 2 * e + 4 = (2 * a + 2 * e + 2) + 1 + 1 from by ring]
    step fm; step fm; finish
  have h4 : ⟨(2 : ℕ), 0, 2 * a + 2 * e + 2, a + 2 * e + 2, 0⟩ [fm]⊢*
      ⟨3 * a + 3 * e + 5, 0, 0, e + 1, a + e + 1⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show 2 * a + 2 * e + 2 = 0 + 2 * (a + e + 1) from by ring,
        show a + 2 * e + 2 = (e + 1) + (a + e + 1) from by ring]
    have := r2r1r1_chain (a + e + 1) 1 0 (e + 1) 0
    rw [show 1 + 3 * (a + e + 1) + 1 = 3 * a + 3 * e + 5 from by ring,
        show (0 : ℕ) + (a + e + 1) = a + e + 1 from by ring] at this; exact this
  have h5 : ⟨3 * a + 3 * e + 5, (0 : ℕ), 0, e + 1, a + e + 1⟩ [fm]⊢*
      ⟨3 * a + 2 * e + 4, 2 * e + 2, 0, 0, a + 2 * e + 2⟩ := by
    have := r2_chain (e + 1) (3 * a + 2 * e + 4) 0 0 (a + e + 1)
    rw [show (0 : ℕ) + 2 * (e + 1) = 2 * e + 2 from by ring,
        show (a + e + 1) + (e + 1) = a + 2 * e + 2 from by ring,
        show (3 * a + 2 * e + 4) + (e + 1) = 3 * a + 3 * e + 5 from by ring,
        show (0 : ℕ) + (e + 1) = e + 1 from by ring] at this; exact this
  have h6 : ⟨3 * a + 2 * e + 4, 2 * e + 2, (0 : ℕ), 0, a + 2 * e + 2⟩ [fm]⊢*
      ⟨3 * a + 5 * e + 7, 0, 0, 0, a + 3 * e + 3⟩ := by
    rw [show 3 * a + 2 * e + 4 = (3 * a + 2 * e + 3) + 1 from by ring,
        show 2 * e + 2 = 0 + 2 * (e + 1) from by ring]
    have := r3r1r1_chain (e + 1) (3 * a + 2 * e + 3) 0 (a + 2 * e + 2)
    rw [show (3 * a + 2 * e + 3) + 3 * (e + 1) + 1 = 3 * a + 5 * e + 7 from by ring,
        show (a + 2 * e + 2) + (e + 1) = a + 3 * e + 3 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h3
        (stepStar_trans h4 (stepStar_trans h5 h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + e + 2, 0, 0, 0, e⟩) ⟨0, 2⟩
  intro ⟨a, e⟩; refine ⟨⟨2 * a + 2 * e + 2, a + 3 * e + 3⟩, ?_⟩
  dsimp only
  have := main_trans a e
  rw [show (2 * a + 2 * e + 2) + (a + 3 * e + 3) + 2 = 3 * a + 5 * e + 7 from by ring]
  exact this
