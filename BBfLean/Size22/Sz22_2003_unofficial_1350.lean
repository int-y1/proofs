import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1350: [63/10, 363/2, 4/77, 5/3, 2/11]

Vector representation:
```
-1  2 -1  1  0
-1  1  0  0  2
 2  0  0 -1 -1
 0 -1  1  0  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1350

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 chain: transfer b to c
theorem b_to_c : ∀ k, ∀ b c, ⟨0, b + k, c, 0, e⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1))
    ring_nf; finish

-- R1,R1,R3 round
theorem round (b c d e : ℕ) : ⟨2, b, c + 2, d, e + 1⟩ [fm]⊢* ⟨2, b + 4, c, d + 1, e⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Spiral phase (even c)
theorem spiral_even : ∀ k, ∀ b d e, ⟨2, b, 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 4 * k, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · simp; exists 0
  · rw [show 2 * (k + 1) = (2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans (round b (2 * k) d (e + k))
    apply stepStar_trans (ih (b + 4) (d + 1) e)
    ring_nf; finish

-- Spiral phase (odd c)
theorem spiral_odd : ∀ k, ∀ b d e, ⟨2, b, 2 * k + 1, d, e + k + 1⟩ [fm]⊢* ⟨1, b + 4 * k + 2, 0, d + k + 1, e + 1⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    apply stepStar_trans (round b (2 * k + 1) d (e + k + 1))
    apply stepStar_trans (ih (b + 4) (d + 1) e)
    ring_nf; finish

-- Drain phase: R3,R2,R2 repeated k times
theorem drain : ∀ k, ∀ b e, ⟨0, b, 0, k, e + 1⟩ [fm]⊢* ⟨0, b + 2 * k, 0, 0, e + 1 + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · simp; exists 0
  · step fm; step fm; step fm
    show ⟨0, b + 1 + 1, 0, k, e + 2 + 2⟩ [fm]⊢* _
    rw [show b + 1 + 1 = (b + 2 : ℕ) from by ring,
        show e + 2 + 2 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (b + 2) (e + 3))
    ring_nf; finish

-- Main transition for even c: (0,0,2k+1,0,e+2) →⁺ (0,0,6k+4,0,e+2k+4)
theorem main_trans_even (k e : ℕ) (he : e ≥ k) :
    ⟨0, 0, 2 * k + 1, 0, e + 2⟩ [fm]⊢⁺ ⟨0, 0, 6 * k + 4, 0, e + 2 * k + 4⟩ := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + k := ⟨e - k, by omega⟩
  step fm; step fm; step fm
  show ⟨2, 2, 2 * k, 0, e' + k⟩ [fm]⊢* _
  apply stepStar_trans (spiral_even k 2 0 e')
  -- Now at (2, 2+4k, 0, k, e')
  step fm; step fm
  show ⟨0, 2 + 4 * k + 1 + 1, 0, 0 + k, e' + 2 + 2⟩ [fm]⊢* _
  rw [show 2 + 4 * k + 1 + 1 = (4 + 4 * k : ℕ) from by ring,
      show 0 + k = k from by ring,
      show e' + 2 + 2 = (e' + 3) + 1 from by ring]
  apply stepStar_trans (drain k (4 + 4 * k) (e' + 3))
  rw [show 4 + 4 * k + 2 * k = 4 + 6 * k from by ring,
      show e' + 3 + 1 + 3 * k = e' + k + 2 * k + 4 from by ring]
  rw [show (4 + 6 * k : ℕ) = 0 + (4 + 6 * k) from by ring]
  apply stepStar_trans (b_to_c (4 + 6 * k) 0 0)
  rw [show 0 + (4 + 6 * k) = 6 * k + 4 from by ring]; finish

-- Main transition for odd c: (0,0,2k+2,0,e+2) →⁺ (0,0,6k+7,0,e+2k+5)
theorem main_trans_odd (k e : ℕ) (he : e ≥ k + 1) :
    ⟨0, 0, 2 * k + 2, 0, e + 2⟩ [fm]⊢⁺ ⟨0, 0, 6 * k + 7, 0, e + 2 * k + 5⟩ := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + (k + 1) := ⟨e - (k + 1), by omega⟩
  step fm; step fm; step fm
  show ⟨2, 2, 2 * k + 1, 0, e' + k + 1⟩ [fm]⊢* _
  apply stepStar_trans (spiral_odd k 2 0 e')
  -- now at (1, 4*k+4, 0, k+1, e'+1)
  step fm
  -- R2: (0, 4*k+5, 0, k+1, e'+3)
  show ⟨0, 2 + 4 * k + 2 + 1, 0, 0 + k + 1, e' + 1 + 2⟩ [fm]⊢* _
  rw [show 2 + 4 * k + 2 + 1 = (4 * k + 5 : ℕ) from by ring,
      show 0 + k + 1 = k + 1 from by ring,
      show e' + 1 + 2 = (e' + 2) + 1 from by ring]
  apply stepStar_trans (drain (k + 1) (4 * k + 5) (e' + 2))
  rw [show 4 * k + 5 + 2 * (k + 1) = (6 * k + 7 : ℕ) from by ring,
      show e' + 2 + 1 + 3 * (k + 1) = e' + (k + 1) + 2 * k + 5 from by ring]
  rw [show (6 * k + 7 : ℕ) = 0 + (6 * k + 7) from by ring]
  apply stepStar_trans (b_to_c (6 * k + 7) 0 0)
  rw [show 0 + (6 * k + 7) = 6 * k + 7 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c, 0, e⟩ ∧ c ≥ 1 ∧ 2 * e ≥ c + 3)
  · intro q ⟨c, e, hq, hc, he⟩; subst hq
    rcases Nat.even_or_odd c with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- c even: c = 2K, K ≥ 1
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      -- c = 2*(k+1) = 2*k+2
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
      refine ⟨⟨0, 0, 6 * k + 7, 0, e' + 2 * k + 5⟩,
        ⟨6 * k + 7, e' + 2 * k + 5, rfl, by omega, by omega⟩, ?_⟩
      exact main_trans_odd k e' (by omega)
    · -- c odd: c = 2K+1
      subst hK
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
      refine ⟨⟨0, 0, 6 * K + 4, 0, e' + 2 * K + 4⟩,
        ⟨6 * K + 4, e' + 2 * K + 4, rfl, by omega, by omega⟩, ?_⟩
      exact main_trans_even K e' (by omega)
  · exact ⟨1, 2, rfl, by omega, by omega⟩
