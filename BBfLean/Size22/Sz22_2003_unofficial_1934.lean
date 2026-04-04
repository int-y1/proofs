import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1934: [9/70, 275/2, 2/15, 7/11, 6/7]

Vector representation:
```
-1  2 -1 -1  0
-1  0  2  0  1
 1 -1 -1  0  0
 0  0  0  1 -1
 1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1934

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨(0 : ℕ), 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem R1R3_chain : ∀ j, ⟨1, b, c + 2 * j, d + j, 0⟩ [fm]⊢* ⟨1, b + j, c, d, 0⟩ := by
  intro j; induction' j with j ih generalizing b c d
  · exists 0
  · rw [show c + 2 * (j + 1) = (c + 2 * j + 1) + 1 from by ring,
        show d + (j + 1) = (d + j) + 1 from by ring]
    step fm
    rw [show c + 2 * j + 1 = (c + 2 * j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1) (c := c) (d := d))
    ring_nf; finish

theorem tail_step : ⟨1, b + 1, 0, d + 1, 0⟩ [fm]⊢* ⟨1, b + 3, 0, d, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem tail_loop : ∀ j, ⟨1, b + 1, 0, d + j, 0⟩ [fm]⊢* ⟨1, b + 1 + 2 * j, 0, d, 0⟩ := by
  intro j; induction' j with j ih generalizing b d
  · exists 0
  · rw [show d + (j + 1) = (d + j) + 1 from by ring]
    apply stepStar_trans (tail_step (b := b) (d := d + j))
    rw [show b + 3 = (b + 2) + 1 from by ring]
    apply stepStar_trans (ih (b := b + 2) (d := d))
    ring_nf; finish

theorem R2R3_drain : ∀ j, ⟨1, j, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + j + 2, 0, e + j + 1⟩ := by
  intro j; induction' j with j ih generalizing c e
  · step fm; finish
  · step fm; step fm
    apply stepStar_trans (ih (c := c + 1) (e := e + 1))
    ring_nf; finish

theorem odd_trans : ∀ m,
    ⟨0, 0, 2 * m + 9, 2 * m + 8, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * m + 12, 3 * m + 11, 0⟩ := by
  intro m
  rw [show 2 * m + 8 = (2 * m + 7) + 1 from by ring]
  step fm
  rw [show 2 * m + 9 = 3 + 2 * (m + 3) from by ring,
      show 2 * m + 7 = (m + 4) + (m + 3) from by ring]
  apply stepStar_trans (R1R3_chain (m + 3) (b := 1) (c := 3) (d := m + 4))
  rw [show 1 + (m + 3) = m + 4 from by ring,
      show (3 : ℕ) = 2 + 1 from by ring, show m + 4 = (m + 3) + 1 from by ring]
  step fm
  rw [show m + 6 = (m + 5) + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring, show m + 3 = (m + 2) + 1 from by ring]
  step fm
  rw [show m + 2 = (m + 1) + 1 from by ring]
  step fm
  rw [show m + 8 = (m + 7) + 1 from by ring,
      show m + 1 = 0 + (m + 1) from by ring]
  apply stepStar_trans (tail_loop (m + 1) (b := m + 7) (d := 0))
  rw [show (m + 7) + 1 + 2 * (m + 1) = 3 * m + 10 from by ring]
  apply stepStar_trans (R2R3_drain (3 * m + 10) (c := 0) (e := 0))
  rw [show 0 + (3 * m + 10) + 2 = 3 * m + 12 from by ring,
      show 0 + (3 * m + 10) + 1 = 3 * m + 11 from by ring]
  apply stepStar_trans (e_to_d (3 * m + 11) (c := 3 * m + 12) (d := 0))
  ring_nf; finish

theorem even_trans : ∀ m,
    ⟨0, 0, 2 * m + 10, 2 * m + 9, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * m + 14, 3 * m + 13, 0⟩ := by
  intro m
  rw [show 2 * m + 9 = (2 * m + 8) + 1 from by ring]
  step fm
  rw [show 2 * m + 10 = 2 + 2 * (m + 4) from by ring,
      show 2 * m + 8 = (m + 4) + (m + 4) from by ring]
  apply stepStar_trans (R1R3_chain (m + 4) (b := 1) (c := 2) (d := m + 4))
  rw [show 1 + (m + 4) = m + 5 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring, show m + 4 = (m + 3) + 1 from by ring]
  step fm
  rw [show m + 7 = (m + 6) + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show m + 6 = (m + 5) + 1 from by ring,
      show m + 3 = 0 + (m + 3) from by ring]
  apply stepStar_trans (tail_loop (m + 3) (b := m + 5) (d := 0))
  rw [show (m + 5) + 1 + 2 * (m + 3) = 3 * m + 12 from by ring]
  apply stepStar_trans (R2R3_drain (3 * m + 12) (c := 0) (e := 0))
  rw [show 0 + (3 * m + 12) + 2 = 3 * m + 14 from by ring,
      show 0 + (3 * m + 12) + 1 = 3 * m + 13 from by ring]
  apply stepStar_trans (e_to_d (3 * m + 13) (c := 3 * m + 14) (d := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 9, 8, 0⟩) (by execute fm 114)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, n + 9, n + 8, 0⟩)
  · intro c ⟨n, hq⟩; subst hq
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      refine ⟨⟨0, 0, 3 * m + 12, 3 * m + 11, 0⟩, ⟨3 * m + 3, ?_⟩, ?_⟩
      · show (0, 0, 3 * m + 12, 3 * m + 11, 0) = (0, 0, 3 * m + 3 + 9, 3 * m + 3 + 8, 0)
        ring_nf
      · show ⟨0, 0, m + m + 9, m + m + 8, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * m + 12, 3 * m + 11, 0⟩
        rw [show m + m = 2 * m from by ring]
        exact odd_trans m
    · subst hm
      refine ⟨⟨0, 0, 3 * m + 14, 3 * m + 13, 0⟩, ⟨3 * m + 5, ?_⟩, ?_⟩
      · show (0, 0, 3 * m + 14, 3 * m + 13, 0) = (0, 0, 3 * m + 5 + 9, 3 * m + 5 + 8, 0)
        ring_nf
      · show ⟨0, 0, 2 * m + 1 + 9, 2 * m + 1 + 8, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * m + 14, 3 * m + 13, 0⟩
        rw [show 2 * m + 1 + 9 = 2 * m + 10 from by ring,
            show 2 * m + 1 + 8 = 2 * m + 9 from by ring]
        exact even_trans m
  · exact ⟨0, rfl⟩
