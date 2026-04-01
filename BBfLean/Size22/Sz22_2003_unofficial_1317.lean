import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1317: [63/10, 143/2, 4/33, 5/7, 14/13]

Vector representation:
```
-1  2 -1  1  0  0
-1  0  0  0  1  1
 2 -1  0  0 -1  0
 0  0  1 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1317

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

-- R4 repeated: move d to c
theorem d_to_c : ∀ k C D, ⟨0, 0, C, D + k, e, f⟩ [fm]⊢* ⟨0, 0, C + k, D, e, f⟩ := by
  intro k; induction' k with k ih <;> intro C D
  · exists 0
  · rw [show D + (k + 1) = (D + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (C + 1) D)
    ring_nf; finish

-- Drain: R3+R2+R2 repeated k times
theorem drain : ∀ k E F, ⟨0, k, 0, d, E + k, F⟩ [fm]⊢* ⟨0, 0, 0, d, E + 2 * k, F + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro E F
  · exists 0
  · rw [show E + (k + 1) = (E + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show (E + k) + 1 + 1 = (E + 2) + k from by ring]
    apply stepStar_trans (ih (E + 2) (F + 2))
    ring_nf; finish

-- Spiral even: (0, b+1, 2*k, d, E+k+1, f) →* (0, b+3*k+1, 0, d+2*k, E+1, f)
theorem spiral_even : ∀ k b d E f, ⟨0, b + 1, 2 * k, d, E + k + 1, f⟩ [fm]⊢* ⟨0, b + 3 * k + 1, 0, d + 2 * k, E + 1, f⟩ := by
  intro k; induction' k with k ih <;> intro b d E f
  · simp; exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show E + (k + 1) + 1 = (E + k + 1) + 1 from by ring]
    step fm
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 3) (d + 2) E f)
    ring_nf; finish

-- Spiral odd: (0, b+1, 2*k+1, d, E+k+1, f) →* (0, b+3*k+2, 0, d+2*k+1, E+1, f+1)
theorem spiral_odd : ∀ k b d E f, ⟨0, b + 1, 2 * k + 1, d, E + k + 1, f⟩ [fm]⊢* ⟨0, b + 3 * k + 2, 0, d + 2 * k + 1, E + 1, f + 1⟩ := by
  intro k; induction' k with k ih <;> intro b d E f
  · simp; step fm; step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show E + (k + 1) + 1 = (E + k + 1) + 1 from by ring]
    step fm
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 3) (d + 2) E f)
    ring_nf; finish

-- Transition for d odd: d = 2*k+1
theorem trans_odd (k : ℕ) : ∀ e f, ⟨0, 0, 0, 2 * k + 1, e + 4 * k + 2, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 2, e + 6 * k + 4, f + 6 * k + 4⟩ := by
  intro e f
  have h1 : ⟨0, 0, 0, 2 * k + 1, e + 4 * k + 2, f + 1⟩ [fm]⊢* ⟨0, 0, 2 * k + 1, 0, e + 4 * k + 2, f + 1⟩ := by
    rw [show (2 * k + 1 : ℕ) = 0 + (2 * k + 1) from by ring]
    exact d_to_c (2 * k + 1) 0 0
  have h2 : ⟨0, 0, 2 * k + 1, 0, e + 4 * k + 2, f + 1⟩ [fm]⊢⁺ ⟨0, 2, 2 * k, 2, e + 4 * k + 2, f⟩ := by
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm; finish
  have h3 : ⟨0, 2, 2 * k, 2, e + 4 * k + 2, f⟩ [fm]⊢* ⟨0, 3 * k + 2, 0, 2 * k + 2, e + 3 * k + 2, f⟩ := by
    rw [show e + 4 * k + 2 = (e + 3 * k + 1) + k + 1 from by ring]
    apply stepStar_trans (spiral_even k 1 2 (e + 3 * k + 1) f)
    ring_nf; finish
  have h4 : ⟨0, 3 * k + 2, 0, 2 * k + 2, e + 3 * k + 2, f⟩ [fm]⊢* ⟨0, 0, 0, 2 * k + 2, e + 6 * k + 4, f + 6 * k + 4⟩ := by
    rw [show e + 3 * k + 2 = e + (3 * k + 2) from by ring]
    apply stepStar_trans (drain (3 * k + 2) e f)
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

-- Transition for d even: d = 2*(k+1)
theorem trans_even (k : ℕ) : ∀ e f, ⟨0, 0, 0, 2 * (k + 1), e + 4 * k + 3, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 3, e + 6 * k + 6, f + 6 * k + 7⟩ := by
  intro e f
  have h1 : ⟨0, 0, 0, 2 * (k + 1), e + 4 * k + 3, f + 1⟩ [fm]⊢* ⟨0, 0, 2 * (k + 1), 0, e + 4 * k + 3, f + 1⟩ := by
    rw [show (2 * (k + 1) : ℕ) = 0 + 2 * (k + 1) from by ring]
    exact d_to_c (2 * (k + 1)) 0 0
  have h2 : ⟨0, 0, 2 * (k + 1), 0, e + 4 * k + 3, f + 1⟩ [fm]⊢⁺ ⟨0, 2, 2 * k + 1, 2, e + 4 * k + 3, f⟩ := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm; step fm; finish
  have h3 : ⟨0, 2, 2 * k + 1, 2, e + 4 * k + 3, f⟩ [fm]⊢* ⟨0, 3 * k + 3, 0, 2 * k + 3, e + 3 * k + 3, f + 1⟩ := by
    rw [show e + 4 * k + 3 = (e + 3 * k + 2) + k + 1 from by ring]
    apply stepStar_trans (spiral_odd k 1 2 (e + 3 * k + 2) f)
    ring_nf; finish
  have h4 : ⟨0, 3 * k + 3, 0, 2 * k + 3, e + 3 * k + 3, f + 1⟩ [fm]⊢* ⟨0, 0, 0, 2 * k + 3, e + 6 * k + 6, f + 6 * k + 7⟩ := by
    rw [show e + 3 * k + 3 = e + (3 * k + 3) from by ring]
    apply stepStar_trans (drain (3 * k + 3) e (f + 1))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2, 1⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e f, q = ⟨0, 0, 0, d, e, f⟩ ∧ d ≥ 1 ∧ e ≥ 2 * d ∧ f ≥ 1)
  · intro c ⟨d, e, f, hq, hd, he, hf⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 4 * k + 3 := ⟨e - (4 * k + 3), by omega⟩
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 2 * k + 3, e' + 6 * k + 6, f' + 6 * k + 7⟩,
        ⟨2 * k + 3, e' + 6 * k + 6, f' + 6 * k + 7, rfl, by omega, by omega, by omega⟩,
        trans_even k e' f'⟩
    · subst hK
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 4 * K + 2 := ⟨e - (4 * K + 2), by omega⟩
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 2 * K + 2, e' + 6 * K + 4, f' + 6 * K + 4⟩,
        ⟨2 * K + 2, e' + 6 * K + 4, f' + 6 * K + 4, rfl, by omega, by omega, by omega⟩,
        trans_odd K e' f'⟩
  · exact ⟨1, 2, 1, rfl, by omega, by omega, by omega⟩
