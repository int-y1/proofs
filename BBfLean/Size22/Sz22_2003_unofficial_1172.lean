import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1172: [5/6, 49/2, 44/35, 1/5, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  0 -1  0  0
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1172

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem round : ⟨0, b + 2, c + 1, d + 1, f⟩ [fm]⊢* ⟨0, b, c + 2, d, f + 1⟩ := by
  step fm; step fm; step fm; finish

theorem interleave : ∀ k, ⟨0, 2 * k + r, c + 1, D + k, f⟩ [fm]⊢* ⟨0, r, c + k + 1, D, f + k⟩ := by
  intro k; induction' k with k ih generalizing c D f
  · ring_nf; finish
  · rw [show 2 * (k + 1) + r = (2 * k + r) + 2 from by ring,
        show D + (k + 1) = (D + k) + 1 from by ring]
    apply stepStar_trans (round (b := 2 * k + r) (c := c) (d := D + k) (f := f))
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c := c + 1) (D := D) (f := f + 1))
    ring_nf; finish

theorem tail_step : ⟨2, 0, c + 1, d, f⟩ [fm]⊢* ⟨2, 0, c, d + 3, f + 1⟩ := by
  step fm; step fm; step fm; finish

theorem tail_chain : ∀ k, ⟨2, 0, k, d, f⟩ [fm]⊢* ⟨2, 0, 0, d + 3 * k, f + k⟩ := by
  intro k; induction' k with k ih generalizing d f
  · ring_nf; finish
  · apply stepStar_trans (tail_step (c := k) (d := d) (f := f))
    apply stepStar_trans (ih (d := d + 3) (f := f + 1))
    ring_nf; finish

theorem even_trans :
    ⟨2, 0, 0, D + k + 3, 2 * k + 2⟩ [fm]⊢⁺ ⟨2, 0, 0, D + 3 * k + 7, 2 * k + 3⟩ := by
  step fm; step fm
  rw [show D + k + 3 + 2 + 2 = D + k + 7 from by ring,
      show 2 * k + 2 = 0 + (2 * k + 2) from by ring]
  apply stepStar_trans (e_to_b (2 * k + 2) (b := 0) (d := D + k + 7) (e := 0))
  rw [show (0 : ℕ) + (2 * k + 2) = 2 * (k + 1) from by ring]
  step fm
  rw [show 2 * (k + 1) = 2 * (k + 1) + 0 from by ring,
      show D + k + 6 = (D + 5) + (k + 1) from by ring]
  apply stepStar_trans (interleave (k + 1) (r := 0) (c := 0) (D := D + 5) (f := 0))
  rw [show 0 + (k + 1) + 1 = k + 2 from by ring,
      show (0 : ℕ) + (k + 1) = k + 1 from by ring]
  step fm
  rw [show k + 2 = (k + 1) + 1 from by ring]
  apply stepStar_trans (tail_chain (k + 1) (d := D + 4) (f := k + 2))
  ring_nf; finish

theorem odd_trans :
    ⟨2, 0, 0, D + k + 3, 2 * k + 1⟩ [fm]⊢⁺ ⟨2, 0, 0, D + 3 * k + 6, 2 * k + 2⟩ := by
  step fm; step fm
  rw [show D + k + 3 + 2 + 2 = D + k + 7 from by ring,
      show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_trans (e_to_b (2 * k + 1) (b := 0) (d := D + k + 7) (e := 0))
  rw [show (0 : ℕ) + (2 * k + 1) = 2 * k + 1 from by ring]
  step fm
  rw [show D + k + 6 = (D + 6) + k from by ring]
  apply stepStar_trans (interleave k (r := 1) (c := 0) (D := D + 6) (f := 0))
  rw [show 0 + k + 1 = k + 1 from by ring,
      show (0 : ℕ) + k = k from by ring]
  step fm; step fm; step fm; step fm
  rw [show k + 1 + 1 = k + 2 from by ring]
  apply stepStar_trans (tail_chain k (d := D + 6) (f := k + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 3, 2⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨2, 0, 0, d, e + 2⟩ ∧ d ≥ e + 3)
  · intro c ⟨d, e, hq, hd⟩; subst hq
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- e = 2k (even), so e+2 = 2k+2
      subst hk
      obtain ⟨D, rfl⟩ : ∃ D, d = D + k + 3 := ⟨d - k - 3, by omega⟩
      have h1 : (2 * k + 1 + 2 : ℕ) = 2 * k + 3 := by omega
      refine ⟨⟨2, 0, 0, D + 3 * k + 7, 2 * k + 3⟩,
        ⟨D + 3 * k + 7, 2 * k + 1, by rw [h1], by omega⟩, ?_⟩
      · show ⟨2, 0, 0, D + k + 3, k + k + 2⟩ [fm]⊢⁺ ⟨2, 0, 0, D + 3 * k + 7, 2 * k + 3⟩
        rw [show k + k + 2 = 2 * k + 2 from by ring]
        exact even_trans
    · -- e = 2k+1 (odd), so e+2 = 2k+3
      subst hk
      obtain ⟨D, rfl⟩ : ∃ D, d = D + (k + 1) + 3 := ⟨d - (k + 1) - 3, by omega⟩
      have h1 : (2 * k + 2 + 2 : ℕ) = 2 * k + 4 := by omega
      refine ⟨⟨2, 0, 0, D + 3 * (k + 1) + 6, 2 * k + 4⟩,
        ⟨D + 3 * (k + 1) + 6, 2 * k + 2, by rw [h1], by omega⟩, ?_⟩
      · show ⟨2, 0, 0, D + (k + 1) + 3, 2 * k + 1 + 2⟩ [fm]⊢⁺
            ⟨2, 0, 0, D + 3 * (k + 1) + 6, 2 * k + 4⟩
        rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 from by ring,
            show 2 * k + 4 = 2 * (k + 1) + 2 from by ring]
        exact odd_trans
  · exact ⟨3, 0, rfl, by omega⟩
