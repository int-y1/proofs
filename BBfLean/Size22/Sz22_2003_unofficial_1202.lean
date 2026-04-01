import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1202: [5/6, 539/2, 4/35, 3/11, 242/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  0
 0  1  0  0 -1
 1  0  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1202

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R4 repeated: move e to b. (0, b, 0, d, e+k) →* (0, b+k, 0, d, e).
theorem e_to_b : ∀ k, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R3+R2+R2 chain: (0, 0, c+k, d+1, e) →* (0, 0, c, d+3*k+1, e+2*k).
theorem r3r2r2_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 3 * k + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 2))
    ring_nf; finish

-- Inner loop: 3-step round. (1, b+2*k, c, d+k, 2) →* (1, b, c+k, d, 2).
theorem inner_round : ∀ k, ∀ b c d, ⟨(1 : ℕ), b + 2 * k, c, d + k, 2⟩ [fm]⊢* ⟨1, b, c + k, d, 2⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih b (c + 1) d)
    ring_nf; finish

-- Odd exit: (1, 1, c, d+1, 2) →* (0, 0, c, d+4, 4).
theorem odd_exit : ⟨(1 : ℕ), 1, c, d + 1, 2⟩ [fm]⊢* ⟨0, 0, c, d + 4, 4⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Full transition from (0, 0, 0, D+1, E) to next canonical via even path.
-- When E = 2*(k+1) and D+1 >= k+2, i.e., D >= k+1.
-- We do: e_to_b, R5, inner_round, R2, r3r2r2_chain.
-- From (0, 2*(k+1), 0, D+1, 0):
--   R5: (1, 2*(k+1), 0, D, 2)
--   inner_round(k+1): need 2*(k+1) = 0 + 2*(k+1) and D = (D - k - 1) + (k+1)
--     result: (1, 0, k+1, D-k-1, 2)
--   R2: (0, 0, k+1, D-k+1, 3)
--   r3r2r2(k+1): (0, 0, 0, D-k+1+3*(k+1), 3+2*(k+1)) = (0, 0, 0, D+2k+4, 2k+5)

-- Even transition: (0, 0, 0, d+k+2, 2*k+2) ⊢⁺ (0, 0, 0, d+3*k+5, 2*k+5).
-- Here d is the "excess" above k+1 needed for inner loop.
-- Parametrized with d+k+1+1 in 4th position.
theorem even_trans : ∀ d k, ⟨(0 : ℕ), 0, 0, d + k + 2, 2 * k + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, d + 3 * k + 5, 2 * k + 5⟩ := by
  intro d k
  -- Rewrite to prepare for e_to_b
  rw [show 2 * k + 2 = 0 + (2 * k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * k + 2) (b := 0) (d := d + k + 2) (e := 0))
  simp only [Nat.zero_add]
  -- Now at (0, 2*k+2, 0, d+k+2, 0). R5 needs d+k+2 = (d+k+1)+1
  rw [show d + k + 2 = (d + k + 1) + 1 from by ring]
  step fm  -- R5: (1, 2*k+2, 0, d+k+1, 2)
  -- Now at (1, 2*k+2, 0, d+k+1, 2). For inner_round(k+1): need b + 2*(k+1) and d' + (k+1)
  -- 2*k+2 = 0 + 2*(k+1) and d+k+1 = d + (k+1)
  rw [show 2 * k + 2 = 0 + 2 * (k + 1) from by ring,
      show d + k + 1 = d + (k + 1) from by ring]
  apply stepStar_trans (inner_round (k + 1) (b := 0) (c := 0) (d := d))
  simp only [Nat.zero_add]
  -- Now at (1, 0, k+1, d, 2). R2.
  step fm  -- R2: (0, 0, k+1, d+2, 3)
  -- For r3r2r2_chain(k+1): need c + (k+1) and d' + 1
  rw [show k + 1 = 0 + (k + 1) from by ring,
      show d + 2 = (d + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (k + 1) 0 (d + 1) 3)
  ring_nf; finish

-- Odd transition: (0, 0, 0, d+k+2, 2*k+1) ⊢⁺ (0, 0, 0, d+3*k+4, 2*k+4).
theorem odd_trans : ∀ d k, ⟨(0 : ℕ), 0, 0, d + k + 2, 2 * k + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, d + 3 * k + 4, 2 * k + 4⟩ := by
  intro d k
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * k + 1) (b := 0) (d := d + k + 2) (e := 0))
  simp only [Nat.zero_add]
  -- Now at (0, 2*k+1, 0, d+k+2, 0). R5.
  rw [show d + k + 2 = (d + k + 1) + 1 from by ring]
  step fm  -- R5: (1, 2*k+1, 0, d+k+1, 2)
  -- For inner_round(k): need 1 + 2*k and (d+1) + k
  rw [show 2 * k + 1 = 1 + 2 * k from by ring,
      show d + k + 1 = (d + 1) + k from by ring]
  apply stepStar_trans (inner_round k (b := 1) (c := 0) (d := d + 1))
  simp only [Nat.zero_add]
  -- Now at (1, 1, k, d+1, 2). odd_exit needs d+1 format.
  apply stepStar_trans (odd_exit (c := k) (d := d))
  -- Now at (0, 0, k, d+4, 4). r3r2r2_chain(k).
  rw [show (k : ℕ) = 0 + k from by ring,
      show d + 4 = (d + 3) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain k 0 (d + 3) 4)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ e ≥ 1 ∧ 2 * d ≥ e + 2)
  · intro c ⟨d, e, hq, he, hd⟩; subst hq
    rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- e even: e = K + K = 2*K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      -- e = 2*K >= 2, so K >= 1
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      -- e = 2*(k+1) = 2*k+2. Need d >= k+2.
      obtain ⟨m, rfl⟩ : ∃ m, d = m + k + 2 := ⟨d - k - 2, by omega⟩
      exact ⟨⟨0, 0, 0, m + 3 * k + 5, 2 * k + 5⟩,
        ⟨m + 3 * k + 5, 2 * k + 5, rfl, by omega, by omega⟩, even_trans m k⟩
    · -- e odd: e = 2*K + 1
      subst hK
      -- Need d >= K + 2
      obtain ⟨m, rfl⟩ : ∃ m, d = m + K + 2 := ⟨d - K - 2, by omega⟩
      exact ⟨⟨0, 0, 0, m + 3 * K + 4, 2 * K + 4⟩,
        ⟨m + 3 * K + 4, 2 * K + 4, rfl, by omega, by omega⟩, odd_trans m K⟩
  · exact ⟨2, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1202
