import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1029: [4/45, 5/14, 11/2, 189/11, 5/3]

Vector representation:
```
 2 -2 -1  0  0
-1  0  1 -1  0
-1  0  0  0  1
 0  3  0  1 -1
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1029

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+3, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a B e,
    ⟨a + k, B, (0 : ℕ), 0, e⟩ [fm]⊢* ⟨a, B, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a B e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih a B (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ B d,
    ⟨(0 : ℕ), B, 0, d, k⟩ [fm]⊢* ⟨0, B + 3 * k, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro B d
  · ring_nf; finish
  · rw [show B + 3 * (k + 1) = (B + 3) + 3 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih (B + 3) (d + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a b d,
    ⟨a + 1, b + 2 * k, (0 : ℕ), d + k, 0⟩ [fm]⊢* ⟨a + k + 1, b, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show a + (k + 1) + 1 = (a + 1) + k + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) b d)
    ring_nf; finish

theorem main_trans (n B : ℕ) :
    ⟨2 * n + 3, B, (0 : ℕ), 0, 0⟩ [fm]⊢⁺
    ⟨2 * n + 5, B + 2 * n, 0, 0, 0⟩ := by
  have h1 : ⟨2 * n + 3, B, (0 : ℕ), 0, 0⟩ [fm]⊢*
      ⟨0, B, 0, 0, 2 * n + 3⟩ := by
    have := r3_chain (2 * n + 3) 0 B 0
    simp only [Nat.zero_add] at this; exact this
  have h2 : ⟨(0 : ℕ), B, 0, 0, 2 * n + 3⟩ [fm]⊢*
      ⟨0, B + 3 * (2 * n + 3), 0, 2 * n + 3, 0⟩ := by
    have := r4_chain (2 * n + 3) B 0
    rw [show (0 : ℕ) + (2 * n + 3) = 2 * n + 3 from by ring] at this; exact this
  have h3 : ⟨(0 : ℕ), B + 3 * (2 * n + 3), 0, 2 * n + 3, 0⟩ [fm]⊢⁺
      ⟨2, B + 2 * n + 2 * (2 * n + 3), 0, 2 * n + 3, 0⟩ := by
    rw [show B + 3 * (2 * n + 3) = ((B + 2 * n + 2 * (2 * n + 3)) + 2) + 1 from by ring,
        show (2 * n + 3 : ℕ) = (2 * n + 2) + 1 from by ring]
    step fm
    rw [show (2 * n + 2 + 1 : ℕ) = 2 * n + 3 from by ring,
        show (B + 2 * n + 2 * (2 * n + 3)) + 2 = (B + 2 * n + 2 * (2 * n + 3)) + 2 from by ring]
    step fm; finish
  have h4 : ⟨(2 : ℕ), B + 2 * n + 2 * (2 * n + 3), 0, 2 * n + 3, 0⟩ [fm]⊢*
      ⟨2 * n + 5, B + 2 * n, 0, 0, 0⟩ := by
    have := r2r1_chain (2 * n + 3) 1 (B + 2 * n) 0
    rw [show (1 : ℕ) + 1 = 2 from by ring,
        show (0 : ℕ) + (2 * n + 3) = 2 * n + 3 from by ring,
        show 1 + (2 * n + 3) + 1 = 2 * n + 5 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 0⟩) (by execute fm 14)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, B⟩ ↦ ⟨2 * n + 3, B, 0, 0, 0⟩) ⟨0, 0⟩
  intro ⟨n, B⟩; exact ⟨⟨n + 1, B + 2 * n⟩, main_trans n B⟩
