import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1933: [9/70, 275/2, 2/15, 7/11, 4/7]

Vector representation:
```
-1  2 -1 -1  0
-1  0  2  0  1
 1 -1 -1  0  0
 0  0  0  1 -1
 2  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1933

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ∀ d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih
  · intro d; ring_nf; exists 0
  · intro d; step fm
    apply stepStar_trans (ih (d + 1))
    rw [show d + 1 + k = d + (k + 1) from by ring]; finish

theorem r3r1_chain : ∀ k, ∀ b d, ⟨0, b + 1, c + 2 * k, d + k, 0⟩ [fm]⊢*
    ⟨0, b + k + 1, c, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro b d; ring_nf; exists 0
  · intro b d
    rw [show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    rw [show b + 1 + k + 1 = b + (k + 1) + 1 from by ring]; finish

theorem middle_step : ⟨0, b + 1, 0, d + 3, 0⟩ [fm]⊢* ⟨0, b + 3, 0, d + 2, 0⟩ := by
  execute fm 9

theorem middle_loop : ∀ k, ∀ b d, ⟨0, b + 1, 0, (d + 2) + k, 0⟩ [fm]⊢*
    ⟨0, b + 2 * k + 1, 0, d + 2, 0⟩ := by
  intro k; induction' k with k ih
  · intro b d; ring_nf; exists 0
  · intro b d
    rw [show (d + 2) + (k + 1) = (d + 1 + 2) + k from by ring]
    apply stepStar_trans (ih b (d + 1))
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring,
        show d + 1 + 2 = d + 3 from by ring]
    apply stepStar_trans (middle_step (b := b + 2 * k) (d := d))
    rw [show b + 2 * k + 3 = b + 2 * (k + 1) + 1 from by ring]; finish

theorem final_preamble : ⟨0, b + 1, 0, 2, 0⟩ [fm]⊢* ⟨0, b + 1, 3, 0, 3⟩ := by
  execute fm 7

theorem r3r2_drain : ∀ k, ∀ c, ⟨0, k + 1, c + 1, 0, c + 1⟩ [fm]⊢*
    ⟨0, 0, k + c + 2, 0, k + c + 2⟩ := by
  intro k; induction' k with k ih
  · intro c; step fm; step fm; ring_nf; finish
  · intro c; step fm; step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 1))
    rw [show k + (c + 1) + 2 = (k + 1) + c + 2 from by ring]; finish

theorem odd_fixup : ⟨1, b + 1, 0, d + 1, 0⟩ [fm]⊢* ⟨0, b + 2, 0, d + 1, 0⟩ := by
  execute fm 4

theorem main_even : ⟨0, 0, 2 * m + 10, 0, 2 * m + 10⟩ [fm]⊢⁺
    ⟨0, 0, 3 * m + 13, 0, 3 * m + 13⟩ := by
  apply stepPlus_stepStar_stepPlus
  · step fm; finish
  · apply stepStar_trans (e_to_d (2 * m + 9) 1 (c := 2 * m + 10))
    step fm; step fm; step fm
    rw [show (4 : ℕ) = 3 + 1 from rfl,
        show 2 * m + 8 = 0 + 2 * (m + 4) from by omega]
    rw [show Nat.add 1 (2 * m + 6) = (m + 3) + (m + 4) from by
        show 1 + (2 * m + 6) = (m + 3) + (m + 4); ring]
    apply stepStar_trans (r3r1_chain (m + 4) 3 (m + 3) (c := 0))
    rw [show (0, 3 + (m + 4) + 1, 0, m + 3, (0 : ℕ)) =
        (0, (m + 7) + 1, 0, (0 + 2) + (m + 1), 0) from by ring_nf]
    apply stepStar_trans (middle_loop (m + 1) (m + 7) 0)
    rw [show (0, m + 7 + 2 * (m + 1) + 1, 0, 0 + 2, (0 : ℕ)) =
        (0, (3 * m + 9) + 1, 0, 2, 0) from by ring_nf]
    apply stepStar_trans (final_preamble (b := 3 * m + 9))
    rw [show (0, (3 * m + 9) + 1, 3, 0, (3 : ℕ)) =
        (0, (3 * m + 9) + 1, 2 + 1, 0, 2 + 1) from by ring_nf]
    apply stepStar_trans (r3r2_drain (3 * m + 9) 2)
    rw [show 3 * m + 9 + 2 + 2 = 3 * m + 13 from by ring]; finish

theorem main_odd : ⟨0, 0, 2 * m + 11, 0, 2 * m + 11⟩ [fm]⊢⁺
    ⟨0, 0, 3 * m + 15, 0, 3 * m + 15⟩ := by
  apply stepPlus_stepStar_stepPlus
  · step fm; finish
  · apply stepStar_trans (e_to_d (2 * m + 10) 1 (c := 2 * m + 11))
    step fm; step fm; step fm
    rw [show (4 : ℕ) = 3 + 1 from rfl,
        show 2 * m + 9 = 1 + 2 * (m + 4) from by omega]
    rw [show Nat.add 1 (2 * m + 7) = (m + 4) + (m + 4) from by
        show 1 + (2 * m + 7) = (m + 4) + (m + 4); ring]
    apply stepStar_trans (r3r1_chain (m + 4) 3 (m + 4) (c := 1))
    rw [show (0, 3 + (m + 4) + 1, 1, m + 4, (0 : ℕ)) =
        (0, m + 8, 1, m + 4, 0) from by ring_nf]
    step fm
    rw [show (1, m + 7, 0, m + 4, (0 : ℕ)) =
        (1, (m + 6) + 1, 0, (m + 3) + 1, 0) from by ring_nf]
    apply stepStar_trans (odd_fixup (b := m + 6) (d := m + 3))
    rw [show (0, m + 6 + 2, 0, m + 3 + 1, (0 : ℕ)) =
        (0, (m + 7) + 1, 0, (0 + 2) + (m + 2), 0) from by ring_nf]
    apply stepStar_trans (middle_loop (m + 2) (m + 7) 0)
    rw [show (0, m + 7 + 2 * (m + 2) + 1, 0, 0 + 2, (0 : ℕ)) =
        (0, (3 * m + 11) + 1, 0, 2, 0) from by ring_nf]
    apply stepStar_trans (final_preamble (b := 3 * m + 11))
    rw [show (0, (3 * m + 11) + 1, 3, 0, (3 : ℕ)) =
        (0, (3 * m + 11) + 1, 2 + 1, 0, 2 + 1) from by ring_nf]
    apply stepStar_trans (r3r2_drain (3 * m + 11) 2)
    rw [show 3 * m + 11 + 2 + 2 = 3 * m + 15 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 10, 0, 10⟩) (by execute fm 177)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, n + 10, 0, n + 10⟩)
  · intro c ⟨n, hq⟩; subst hq
    rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      refine ⟨⟨0, 0, 3 * K + 13, 0, 3 * K + 13⟩, ⟨3 * K + 3, by ring_nf⟩, ?_⟩
      show ⟨0, 0, 2 * K + 10, 0, 2 * K + 10⟩ [fm]⊢⁺ _
      exact main_even
    · subst hK
      refine ⟨⟨0, 0, 3 * K + 15, 0, 3 * K + 15⟩, ⟨3 * K + 5, by ring_nf⟩, ?_⟩
      show ⟨0, 0, 2 * K + 1 + 10, 0, 2 * K + 1 + 10⟩ [fm]⊢⁺ _
      rw [show 2 * K + 1 + 10 = 2 * K + 11 from by omega]
      exact main_odd
  · exact ⟨0, rfl⟩

end Sz22_2003_unofficial_1933
