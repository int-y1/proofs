import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1230: [5/6, 5929/2, 44/35, 3/11, 2/3]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  2
 2  0 -1 -1  1
 0  1  0  0 -1
 1 -1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1230

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 chain: drain e into b
theorem e_to_b : ∀ k, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R1R1R3 chain: (2, b+2k, c, d+k, e) ⊢* (2, b, c+k, d, e+k)
theorem r1r1r3_chain : ∀ k, ∀ b c d e, ⟨(2 : ℕ), b + 2 * k, c, d + k, e⟩ [fm]⊢* ⟨2, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    rw [show b + 2 = (b + 1) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show c + k + 1 = c + (k + 1) from by ring]
    finish

-- R3R2R2 chain: (0, 0, c+k, d+1, e) ⊢* (0, 0, c, d+3k+1, e+5k)
theorem r3r2r2_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 3 * k + 1, e + 5 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 5))
    ring_nf; finish

-- Even transition: e = 2k+2, d = m+k+1
-- (0,0,0,m+k+1,2k+2) ⊢⁺ (0,0,0,m+3k+4,6k+5)
theorem even_trans : ∀ m k, ⟨(0 : ℕ), 0, 0, m + k + 1, 2 * k + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, m + 3 * k + 4, 6 * k + 5⟩ := by
  intro m k
  rw [show 2 * k + 2 = 0 + (2 * k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * k + 2) (b := 0) (d := m + k + 1) (e := 0))
  simp only [Nat.zero_add]
  -- (0, 2k+2, 0, m+k+1, 0). R5.
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm
  -- (1, 2k+1, 0, m+k+1, 0). R1.
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring,
      show m + k + 1 = (m + k + 1) from by ring]
  step fm
  -- (0, 2k, 1, m+k+1, 0). R3. Need d≥1: m+k+1≥1. ✓
  rw [show m + k + 1 = (m + k) + 1 from by ring]
  step fm
  -- (2, 2k, 0, m+k, 1). R1R1R3 chain k rounds.
  rw [show 2 * k = 0 + 2 * k from by ring,
      show m + k = m + k from by ring]
  apply stepStar_trans (r1r1r3_chain k 0 0 m 1)
  -- (2, 0, 0+k, m, 1+k). R2.
  step fm
  -- (1, 0, 0+k, m+2, 1+k+2). R2.
  step fm
  -- (0, 0, 0+k, m+2+2, 1+k+2+2). Normalize and apply R3R2R2 chain.
  rw [show 1 + k + 2 + 2 = k + 5 from by ring,
      show m + 2 + 2 = (m + 3) + 1 from by ring,
      show (0 : ℕ) + k = 0 + k from by ring]
  apply stepStar_trans (r3r2r2_chain k 0 (m + 3) (k + 5))
  ring_nf; finish

-- Odd transition: e = 2k+3, d = m+k+1
-- (0,0,0,m+k+1,2k+3) ⊢⁺ (0,0,0,m+3k+5,6k+8)
theorem odd_trans : ∀ m k, ⟨(0 : ℕ), 0, 0, m + k + 1, 2 * k + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, m + 3 * k + 5, 6 * k + 8⟩ := by
  intro m k
  rw [show 2 * k + 3 = 0 + (2 * k + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * k + 3) (b := 0) (d := m + k + 1) (e := 0))
  simp only [Nat.zero_add]
  -- (0, 2k+3, 0, m+k+1, 0). R5.
  rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring]
  step fm
  -- (1, 2k+2, 0, m+k+1, 0). R1.
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm
  -- (0, 2k+1, 1, m+k+1, 0). R3.
  rw [show m + k + 1 = (m + k) + 1 from by ring]
  step fm
  -- (2, 2k+1, 0, m+k, 1). R1R1R3 chain k rounds.
  rw [show 2 * k + 1 = 1 + 2 * k from by ring,
      show m + k = m + k from by ring]
  apply stepStar_trans (r1r1r3_chain k 1 0 m 1)
  simp only [Nat.zero_add]
  -- (2, 1, k, m, 1+k). R1.
  step fm
  -- (1, 0, k+1, m, 1+k). R2.
  step fm
  -- (0, 0, k+1, m+2, 1+k+2). R3R2R2 chain (k+1) rounds.
  rw [show 1 + k + 2 = k + 3 from by ring,
      show k + 1 = 0 + (k + 1) from by ring,
      show m + 2 = (m + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (k + 1) 0 (m + 1) (k + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ e ≥ 2 ∧ 2 * d + 1 ≥ e)
  · intro c ⟨d, e, hq, he, hd⟩; subst hq
    rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- e even: e = K + K = 2*K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, d = m + k + 1 := ⟨d - k - 1, by omega⟩
      exact ⟨⟨0, 0, 0, m + 3 * k + 4, 6 * k + 5⟩,
        ⟨m + 3 * k + 4, 6 * k + 5, rfl, by omega, by omega⟩, even_trans m k⟩
    · -- e odd: e = 2*K + 1
      subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, d = m + k + 1 := ⟨d - k - 1, by omega⟩
      exact ⟨⟨0, 0, 0, m + 3 * k + 5, 6 * k + 8⟩,
        ⟨m + 3 * k + 5, 6 * k + 8, rfl, by omega, by omega⟩, odd_trans m k⟩
  · exact ⟨2, 2, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1230
