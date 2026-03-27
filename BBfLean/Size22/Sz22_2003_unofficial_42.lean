import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #42: [1/15, 49/3, 36/77, 5/49, 33/2]

Vector representation:
```
 0 -1 -1  0  0
 0 -1  0  2  0
 2  2  0 -1 -1
 0  0  1 -2  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_42

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R3/R2/R2 chain: each round does A+=2, D+=3, E-=1
theorem r3r2r2_chain : ∀ k, ∀ A D E,
    ⟨A, 0, 0, D + 1, E + k⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, D + 1 + 3 * k, E⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · exists 0
  rw [show E + (k + 1) = (E + k) + 1 from by ring,
      show D + 1 + 3 * (k + 1) = (D + 1 + 3 * k) + 3 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- R4 drain even
theorem r4_drain : ∀ k, ∀ A C,
    ⟨A, 0, C, 2 * k, 0⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- R4 drain odd
theorem r4_drain_odd : ∀ k, ∀ A C,
    ⟨A, 0, C, 2 * k + 1, 0⟩ [fm]⊢* ⟨A, 0, C + k, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- R5/R1 drain
theorem r5r1_drain : ∀ k, ∀ A E,
    ⟨A + k, 0, k, 0, E⟩ [fm]⊢* ⟨A, 0, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- Transition for e = 0
theorem trans_e0 (a : ℕ) : ⟨a + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 0, 1⟩ := by
  execute fm 15

-- Transition for e = 1
theorem trans_e1 (a : ℕ) : ⟨a + 2, 0, 0, 0, 1⟩ [fm]⊢⁺ ⟨a + 1, 0, 0, 0, 4⟩ := by
  execute fm 20

-- Full even transition: compose R5, R2, chain, R4 drain, bridge, R5/R1 drain
theorem trans_even (a k : ℕ) :
    ⟨a + 1, 0, 0, 0, 2 * k + 2⟩ [fm]⊢⁺ ⟨a + k + 5, 0, 0, 0, 3 * k + 2⟩ := by
  -- R5, R2: 2 steps
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0, 2 * k + 2⟩ = some ⟨a, 1, 0, 0, 2 * k + 3⟩; simp [fm]
  step fm
  -- Now at (a, 0, 0, 2, 2k+3). Do R3/R2/R2 chain for 2k+3 rounds.
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * k + 3 = 0 + (2 * k + 3) from by ring]
  apply stepStar_trans (r3r2r2_chain (2 * k + 3) a 1 0)
  -- Now at (a + 2*(2k+3), 0, 0, 1+1+3*(2k+3), 0) = (a+4k+6, 0, 0, 6k+11, 0)
  -- R4 drain odd: 6k+11 = 2*(3k+5)+1
  rw [show 1 + 1 + 3 * (2 * k + 3) = 2 * (3 * k + 5) + 1 from by ring,
      show a + 2 * (2 * k + 3) = a + 4 * k + 6 from by ring]
  apply stepStar_trans (r4_drain_odd (3 * k + 5) (a + 4 * k + 6) 0)
  -- Now at (a+4k+6, 0, 0+(3k+5), 1, 0) = (a+4k+6, 0, 3k+5, 1, 0)
  -- Bridge: R5, R1, R3, R1, R1 = 5 steps
  rw [show (0 : ℕ) + (3 * k + 5) = (3 * k + 4) + 1 from by ring,
      show a + 4 * k + 6 = (a + 4 * k + 5) + 1 from by ring]
  step fm  -- R5: (a+4k+5, 1, 3k+5, 1, 1)
  rw [show 3 * k + 4 + 1 = (3 * k + 4) + 1 from by ring]
  step fm  -- R1: (a+4k+5, 0, 3k+4, 1, 1)
  step fm  -- R3: (a+4k+7, 2, 3k+4, 0, 0)
  rw [show 3 * k + 4 = (3 * k + 3) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm  -- R1: (a+4k+7, 1, 3k+3, 0, 0)
  rw [show 3 * k + 3 = (3 * k + 2) + 1 from by ring]
  step fm  -- R1: (a+4k+7, 0, 3k+2, 0, 0)
  -- R5/R1 drain: 3k+2 rounds
  rw [show a + 4 * k + 7 = (a + k + 5) + (3 * k + 2) from by ring]
  apply stepStar_trans (r5r1_drain (3 * k + 2) (a + k + 5) 0)
  ring_nf; finish

-- Full odd transition
theorem trans_odd (a k : ℕ) :
    ⟨a + 1, 0, 0, 0, 2 * k + 3⟩ [fm]⊢⁺ ⟨a + k + 1, 0, 0, 0, 3 * k + 7⟩ := by
  -- R5, R2: 2 steps
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0, 2 * k + 3⟩ = some ⟨a, 1, 0, 0, 2 * k + 4⟩; simp [fm]
  step fm
  -- Now at (a, 0, 0, 2, 2k+4). Do R3/R2/R2 chain for 2k+4 rounds.
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * k + 4 = 0 + (2 * k + 4) from by ring]
  apply stepStar_trans (r3r2r2_chain (2 * k + 4) a 1 0)
  -- Now at (a + 2*(2k+4), 0, 0, 1+1+3*(2k+4), 0) = (a+4k+8, 0, 0, 6k+14, 0)
  -- R4 drain even: 6k+14 = 2*(3k+7)
  rw [show 1 + 1 + 3 * (2 * k + 4) = 2 * (3 * k + 7) from by ring,
      show a + 2 * (2 * k + 4) = a + 4 * k + 8 from by ring]
  apply stepStar_trans (r4_drain (3 * k + 7) (a + 4 * k + 8) 0)
  -- Now at (a+4k+8, 0, 0+(3k+7), 0, 0) = (a+4k+8, 0, 3k+7, 0, 0)
  -- R5/R1 drain: 3k+7 rounds
  rw [show (0 : ℕ) + (3 * k + 7) = 3 * k + 7 from by ring,
      show a + 4 * k + 8 = (a + k + 1) + (3 * k + 7) from by ring]
  apply stepStar_trans (r5r1_drain (3 * k + 7) (a + k + 1) 0)
  ring_nf; finish

-- Main transition
theorem main_trans (a e : ℕ) (ha : a ≥ 1) (hinv : e = 1 → a ≥ 2) :
    ∃ a' e', a' ≥ 1 ∧ (e' = 1 → a' ≥ 2) ∧
    ⟨a, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a', 0, 0, 0, e'⟩ := by
  rcases e with _ | _ | e
  · -- e = 0
    obtain ⟨a₀, rfl⟩ : ∃ a₀, a = a₀ + 1 := ⟨a - 1, by omega⟩
    exact ⟨a₀ + 2, 1, by omega, by omega, trans_e0 a₀⟩
  · -- e = 1
    obtain ⟨a₀, rfl⟩ : ∃ a₀, a = a₀ + 2 := ⟨a - 2, by omega⟩
    exact ⟨a₀ + 1, 4, by omega, by omega, trans_e1 a₀⟩
  · -- e >= 2
    obtain ⟨a₀, rfl⟩ : ∃ a₀, a = a₀ + 1 := ⟨a - 1, by omega⟩
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- e even: e + 2 = 2k + 2
      rw [show e + 2 = 2 * k + 2 from by omega]
      exact ⟨a₀ + k + 5, 3 * k + 2, by omega, by omega, trans_even a₀ k⟩
    · -- e odd: e + 2 = 2k + 3
      rw [show e + 2 = 2 * k + 3 from by omega]
      exact ⟨a₀ + k + 1, 3 * k + 7, by omega, by omega, trans_odd a₀ k⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 15)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1 ∧ (e = 1 → a ≥ 2))
  · intro c ⟨a, e, hq, ha, hinv⟩; subst hq
    obtain ⟨a', e', ha', hinv', htrans⟩ := main_trans a e ha hinv
    exact ⟨⟨a', 0, 0, 0, e'⟩, ⟨a', e', rfl, ha', hinv'⟩, htrans⟩
  · exact ⟨2, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_42
