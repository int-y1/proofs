import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1837: [9/10, 77/2, 8/21, 5/7, 14/11]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  1  1
 3 -1  0 -1  0
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1837

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem d_to_c : ∀ k, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    show ⟨0, 0, c + 1, d + k, e⟩ [fm]⊢* ⟨0, 0, c + (k + 1), d, e⟩
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    exact ih

theorem spiral_round : ∀ k, ⟨0, b, c + 4 * k, 0, e + k⟩ [fm]⊢* ⟨0, b + 7 * k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · exists 0
  · rw [show c + 4 * (k + 1) = (c + 4 * k) + 4 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm; step fm
    show ⟨0, b + 7, c + 4 * k, 0, e + k⟩ [fm]⊢* ⟨0, b + 7 * (k + 1), c, 0, e⟩
    rw [show b + 7 * (k + 1) = (b + 7) + 7 * k from by ring]
    exact ih

theorem drain : ∀ k, ⟨0, b + k, 0, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + 2 * k + 1, e + 3 * k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    show ⟨0, b + k, 0, d + 3, e + 3⟩ [fm]⊢* ⟨0, b, 0, d + 2 * (k + 1) + 1, e + 3 * (k + 1)⟩
    rw [show d + 2 * (k + 1) + 1 = (d + 2) + 2 * k + 1 from by ring,
        show e + 3 * (k + 1) = (e + 3) + 3 * k from by ring,
        show d + 3 = (d + 2) + 1 from by ring]
    exact ih

theorem tail_r1 : ⟨0, b, 1, 0, e + 1⟩ [fm]⊢⁺ ⟨0, b + 1, 0, 3, e + 3⟩ := by
  execute fm 6

theorem tail_r3 : ⟨0, b, 3, 0, e + 1⟩ [fm]⊢⁺ ⟨0, b + 4, 0, 3, e + 4⟩ := by
  execute fm 10

-- Spiral n rounds starting from b=0
theorem spiral_from_zero :
    ⟨0, 0, c + 4 * n, 0, e + n⟩ [fm]⊢* ⟨0, 7 * n, c, 0, e⟩ := by
  have := spiral_round n (b := 0) (c := c) (e := e)
  simp only [Nat.zero_add] at this
  exact this

theorem trans_mod1 (hE : E ≥ 4 * n + 1) :
    ⟨0, 0, 0, 4 * n + 1, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 14 * n + 5, E + 20 * n + 5⟩ := by
  have h1 : ⟨0, 0, 0, 4 * n + 1, E⟩ [fm]⊢* ⟨0, 0, 4 * n + 1, 0, E⟩ := by
    rw [show 4 * n + 1 = 0 + (4 * n + 1) from by ring]
    exact d_to_c (4 * n + 1) (c := 0) (d := 0)
  have h2 : ⟨0, 0, 4 * n + 1, 0, E⟩ [fm]⊢* ⟨0, 7 * n, 1, 0, E - n⟩ := by
    have := spiral_from_zero (c := 1) (n := n) (e := E - n)
    rw [show 1 + 4 * n = 4 * n + 1 from by ring,
        show E - n + n = E from by omega] at this
    exact this
  have h3 : ⟨0, 7 * n, 1, 0, E - n⟩ [fm]⊢⁺ ⟨0, 7 * n + 1, 0, 3, E - n - 1 + 3⟩ := by
    rw [show E - n = (E - n - 1) + 1 from by omega]
    exact tail_r1
  have h4 : ⟨0, 7 * n + 1, 0, 3, E - n - 1 + 3⟩ [fm]⊢*
      ⟨0, 0, 0, 14 * n + 5, E + 20 * n + 5⟩ := by
    rw [show 7 * n + 1 = 0 + (7 * n + 1) from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    apply stepStar_trans (drain (7 * n + 1) (b := 0) (d := 2) (e := E - n - 1 + 3))
    rw [show 2 + 2 * (7 * n + 1) + 1 = 14 * n + 5 from by ring,
        show (E - n - 1 + 3) + 3 * (7 * n + 1) = E + 20 * n + 5 from by omega]
    finish
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2 (stepPlus_stepStar_stepPlus h3 h4))

theorem trans_mod3 (hE : E ≥ 4 * n + 3) :
    ⟨0, 0, 0, 4 * n + 3, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 14 * n + 11, E + 20 * n + 15⟩ := by
  have h1 : ⟨0, 0, 0, 4 * n + 3, E⟩ [fm]⊢* ⟨0, 0, 4 * n + 3, 0, E⟩ := by
    rw [show 4 * n + 3 = 0 + (4 * n + 3) from by ring]
    exact d_to_c (4 * n + 3) (c := 0) (d := 0)
  have h2 : ⟨0, 0, 4 * n + 3, 0, E⟩ [fm]⊢* ⟨0, 7 * n, 3, 0, E - n⟩ := by
    have := spiral_from_zero (c := 3) (n := n) (e := E - n)
    rw [show 3 + 4 * n = 4 * n + 3 from by ring,
        show E - n + n = E from by omega] at this
    exact this
  have h3 : ⟨0, 7 * n, 3, 0, E - n⟩ [fm]⊢⁺ ⟨0, 7 * n + 4, 0, 3, E - n - 1 + 4⟩ := by
    rw [show E - n = (E - n - 1) + 1 from by omega]
    exact tail_r3
  have h4 : ⟨0, 7 * n + 4, 0, 3, E - n - 1 + 4⟩ [fm]⊢*
      ⟨0, 0, 0, 14 * n + 11, E + 20 * n + 15⟩ := by
    rw [show 7 * n + 4 = 0 + (7 * n + 4) from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    apply stepStar_trans (drain (7 * n + 4) (b := 0) (d := 2) (e := E - n - 1 + 4))
    rw [show 2 + 2 * (7 * n + 4) + 1 = 14 * n + 11 from by ring,
        show (E - n - 1 + 4) + 3 * (7 * n + 4) = E + 20 * n + 15 from by omega]
    finish
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2 (stepPlus_stepStar_stepPlus h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ D ≥ 1 ∧ E ≥ D ∧ D % 2 = 1)
  · intro c ⟨D, E, hq, hD, hE, hOdd⟩; subst hq
    rcases Nat.even_or_odd (D / 2) with ⟨n, hn⟩ | ⟨n, hn⟩
    · have hD_eq : D = 4 * n + 1 := by omega
      subst hD_eq
      refine ⟨⟨0, 0, 0, 14 * n + 5, E + 20 * n + 5⟩,
        ⟨14 * n + 5, E + 20 * n + 5, rfl, by omega, by omega, by omega⟩,
        trans_mod1 (by omega)⟩
    · have hD_eq : D = 4 * n + 3 := by omega
      subst hD_eq
      refine ⟨⟨0, 0, 0, 14 * n + 11, E + 20 * n + 15⟩,
        ⟨14 * n + 11, E + 20 * n + 15, rfl, by omega, by omega, by omega⟩,
        trans_mod3 (by omega)⟩
  · exact ⟨1, 1, rfl, by omega, by omega, by omega⟩
