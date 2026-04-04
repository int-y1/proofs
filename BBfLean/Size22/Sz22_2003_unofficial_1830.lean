import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1830: [9/10, 5929/2, 2/21, 5/7, 14/11]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  2  2
 1 -1  0 -1  0
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1830

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: move d to c.
theorem d_to_c : ∀ k, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (c := c + 1) (d := d))
    ring_nf; finish

-- One spiral round: R5, R1, R3, R1.
theorem spiral_round : ⟨0, b, c + 2, 0, e + 1⟩ [fm]⊢* ⟨0, b + 3, c, 0, e⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Odd tail: R5, R1, R3, R2.
theorem odd_tail : ⟨0, b, 1, 0, F + 1⟩ [fm]⊢* ⟨0, b + 1, 0, 2, F + 2⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Even spiral: k rounds reduce c from 2k to 0.
theorem spiral_even : ∀ k, ⟨0, b, 2 * k, 0, E + k⟩ [fm]⊢* ⟨0, b + 3 * k, 0, 0, E⟩ := by
  intro k; induction' k with k ih generalizing b E
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show E + (k + 1) = E + k + 1 from by ring]
    apply stepStar_trans (spiral_round (b := b) (c := 2 * k) (e := E + k))
    show ⟨0, b + 3, 2 * k, 0, E + k⟩ [fm]⊢* ⟨0, b + 3 * (k + 1), 0, 0, E⟩
    rw [show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring]
    exact ih (b := b + 3) (E := E)

-- Odd spiral: k even rounds then odd tail.
theorem spiral_odd : ∀ k, ⟨0, b, 2 * k + 1, 0, E + k + 1⟩ [fm]⊢*
    ⟨0, b + 3 * k + 1, 0, 2, E + 2⟩ := by
  intro k; induction' k with k ih generalizing b E
  · exact odd_tail
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show E + (k + 1) + 1 = (E + k + 1) + 1 from by ring]
    apply stepStar_trans (spiral_round (b := b) (c := 2 * k + 1) (e := E + k + 1))
    show ⟨0, b + 3, 2 * k + 1, 0, E + k + 1⟩ [fm]⊢* ⟨0, b + 3 * (k + 1) + 1, 0, 2, E + 2⟩
    rw [show b + 3 * (k + 1) + 1 = (b + 3) + 3 * k + 1 from by ring]
    exact ih (b := b + 3) (E := E)

-- Drain R3+R2: each round b decreases by 1, d increases by 1, e increases by 2.
theorem drain_R3R2 : ∀ B, ⟨0, B + 1, 0, D + 1, E⟩ [fm]⊢* ⟨0, 0, 0, D + B + 2, E + 2 * B + 2⟩ := by
  intro B; induction' B with B ih generalizing D E
  · step fm; step fm; finish
  · step fm; step fm
    show ⟨0, B + 1, 0, D + 2, E + 2⟩ [fm]⊢* ⟨0, 0, 0, D + (B + 1) + 2, E + 2 * (B + 1) + 2⟩
    rw [show D + (B + 1) + 2 = (D + 1) + B + 2 from by ring,
        show E + 2 * (B + 1) + 2 = (E + 2) + 2 * B + 2 from by ring,
        show D + 2 = (D + 1) + 1 from by ring]
    exact ih (D := D + 1) (E := E + 2)

-- Full drain from (0, B+1, 0, 0, E+1): R5 + R2 + drain_R3R2.
theorem drain_full : ⟨0, B + 1, 0, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, B + 4, E + 2 * B + 4⟩ := by
  step fm; step fm
  show ⟨0, B + 1, 0, 3, E + 2⟩ [fm]⊢* ⟨0, 0, 0, B + 4, E + 2 * B + 4⟩
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show B + 4 = 2 + B + 2 from by ring,
      show E + 2 * B + 4 = (E + 2) + 2 * B + 2 from by ring]
  exact drain_R3R2 B (D := 2) (E := E + 2)

-- Even transition: (0,0,0,2*(k+1),E+k+2) ->⁺ (0,0,0,3*k+6,E+6*k+8)
theorem even_trans : ⟨0, 0, 0, 2 * (k + 1), E + k + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 3 * k + 6, E + 6 * k + 8⟩ := by
  rw [show 2 * (k + 1) = 0 + 2 * (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * (k + 1)) (c := 0) (d := 0) (e := E + k + 2))
  rw [show (0 : ℕ) + 2 * (k + 1) = 2 * (k + 1) from by ring,
      show E + k + 2 = (E + 1) + (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (spiral_even (k + 1) (b := 0) (E := E + 1))
  show ⟨0, 0 + 3 * (k + 1), 0, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * k + 6, E + 6 * k + 8⟩
  rw [show (0 : ℕ) + 3 * (k + 1) = (3 * k + 2) + 1 from by ring,
      show 3 * k + 6 = (3 * k + 2) + 4 from by ring,
      show E + 6 * k + 8 = E + 2 * (3 * k + 2) + 4 from by ring]
  exact drain_full (B := 3 * k + 2) (E := E)

-- Odd transition: extract first R4 step for stepPlus.
theorem odd_trans : ⟨0, 0, 0, 2 * k + 1, E + k + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 3 * k + 3, E + 6 * k + 4⟩ := by
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm
  show ⟨0, 0, 1, 2 * k, E + k + 1⟩ [fm]⊢* ⟨0, 0, 0, 3 * k + 3, E + 6 * k + 4⟩
  rw [show (1 : ℕ) = 1 from rfl,
      show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans (d_to_c (2 * k) (c := 1) (d := 0) (e := E + k + 1))
  rw [show (1 : ℕ) + 2 * k = 2 * k + 1 from by ring]
  apply stepStar_trans (spiral_odd k (b := 0) (E := E))
  show ⟨0, 0 + 3 * k + 1, 0, 2, E + 2⟩ [fm]⊢* ⟨0, 0, 0, 3 * k + 3, E + 6 * k + 4⟩
  rw [show (0 : ℕ) + 3 * k + 1 = (3 * k) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show 3 * k + 3 = 1 + (3 * k) + 2 from by ring,
      show E + 6 * k + 4 = (E + 2) + 2 * (3 * k) + 2 from by ring]
  exact drain_R3R2 (3 * k) (D := 1) (E := E + 2)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 2 ∧ e ≥ d)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d even: d = 2*K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨E, rfl⟩ : ∃ E, e = E + k + 2 := ⟨e - k - 2, by omega⟩
      exact ⟨⟨0, 0, 0, 3 * k + 6, E + 6 * k + 8⟩,
        ⟨3 * k + 6, E + 6 * k + 8, rfl, by omega, by omega⟩, even_trans⟩
    · -- d odd: d = 2*K + 1
      subst hK
      obtain ⟨E, rfl⟩ : ∃ E, e = E + K + 1 := ⟨e - K - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 3 * K + 3, E + 6 * K + 4⟩,
        ⟨3 * K + 3, E + 6 * K + 4, rfl, by omega, by omega⟩, odd_trans⟩
  · exact ⟨2, 2, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1830
