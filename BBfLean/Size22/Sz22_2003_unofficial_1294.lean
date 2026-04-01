import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1294: [63/10, 121/2, 12/77, 5/3, 7/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 2  1  0 -1 -1
 0 -1  1  0  0
 0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1294

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: move b to c
theorem b_to_c : ∀ k b c e, ⟨(0 : ℕ), b + k, c, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) e)
    ring_nf; finish

-- R1R1R3 chain: k rounds
theorem r1r1r3_chain : ∀ k B C D E,
    ⟨(2 : ℕ), B, C + 2 * k, D, E + k⟩ [fm]⊢* ⟨(2 : ℕ), B + 5 * k, C, D + k, E⟩ := by
  intro k; induction' k with k ih <;> intro B C D E
  · exists 0
  · rw [show C + 2 * (k + 1) = (C + 2) + 2 * k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    apply stepStar_trans (ih B (C + 2) D (E + 1))
    step fm
    step fm
    step fm
    ring_nf; finish

-- R2R2R3 drain: k rounds
theorem r2r2r3_drain : ∀ k B E,
    ⟨(2 : ℕ), B, 0, k, E⟩ [fm]⊢* ⟨(2 : ℕ), B + k, 0, 0, E + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro B E
  · exists 0
  · step fm
    step fm
    step fm
    apply stepStar_trans (ih (B + 1) (E + 3))
    ring_nf; finish

-- Even transition: b=2k
theorem main_trans_even (k E : ℕ) :
    ⟨(0 : ℕ), 2 * k, 0, 0, E + k + 2⟩ [fm]⊢⁺ ⟨(0 : ℕ), 6 * k + 1, 0, 0, E + 3 * k + 4⟩ := by
  rw [show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_stepPlus_stepPlus (b_to_c (2 * k) 0 0 (E + k + 2))
  rw [show (0 : ℕ) + 2 * k = 2 * k from by ring,
      show E + k + 2 = (E + k + 1) + 1 from by ring]
  step fm  -- R5
  rw [show E + k + 1 = (E + k) + 1 from by ring]
  step fm  -- R3
  rw [show 2 * k = 0 + 2 * k from by ring,
      show E + k = E + k from rfl]
  apply stepStar_trans (r1r1r3_chain k 1 0 0 E)
  rw [show (0 : ℕ) + k = k from by ring]
  apply stepStar_trans (r2r2r3_drain k (1 + 5 * k) E)
  rw [show 1 + 5 * k + k = 6 * k + 1 from by ring]
  step fm  -- R2
  step fm  -- R2
  rw [show E + 3 * k + 2 + 2 = E + 3 * k + 4 from by ring]
  finish

-- Odd transition: b=2k+1
theorem main_trans_odd (k E : ℕ) :
    ⟨(0 : ℕ), 2 * k + 1, 0, 0, E + k + 2⟩ [fm]⊢⁺ ⟨(0 : ℕ), 6 * k + 4, 0, 0, E + 3 * k + 5⟩ := by
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (b_to_c (2 * k + 1) 0 0 (E + k + 2))
  rw [show (0 : ℕ) + (2 * k + 1) = 2 * k + 1 from by ring,
      show E + k + 2 = (E + k + 1) + 1 from by ring]
  step fm  -- R5
  rw [show E + k + 1 = (E + k) + 1 from by ring]
  step fm  -- R3
  rw [show 2 * k + 1 = 1 + 2 * k from by ring,
      show E + k = E + k from rfl]
  apply stepStar_trans (r1r1r3_chain k 1 1 0 E)
  rw [show (0 : ℕ) + k = k from by ring]
  -- State: (2, 1+5k, 1, k, E)
  step fm  -- R1: (1, 1+5k+2, 0, k+1, E)
  step fm  -- R2: (0, 1+5k+2, 0, k+1, E+2)
  -- R3: need d+1 and e+1 patterns
  rw [show E + 2 = (E + 1) + 1 from by ring]
  step fm  -- R3: (2, 1+5k+2+1, 0, k, E+1)
  rw [show 1 + 5 * k + 2 + 1 = 4 + 5 * k from by ring]
  apply stepStar_trans (r2r2r3_drain k (4 + 5 * k) (E + 1))
  rw [show 4 + 5 * k + k = 6 * k + 4 from by ring]
  step fm  -- R2
  step fm  -- R2
  rw [show E + 1 + 3 * k + 2 + 2 = E + 3 * k + 5 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b e, q = ⟨(0 : ℕ), b, 0, 0, e⟩ ∧ e ≥ 2 ∧ 2 * e ≥ b + 4)
  · intro c ⟨b, e, hq, he2, hbe⟩; subst hq
    rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- b even: b = 2k
      rw [show k + k = 2 * k from by ring] at hk; subst hk
      obtain ⟨E, rfl⟩ : ∃ E, e = E + k + 2 := ⟨e - k - 2, by omega⟩
      refine ⟨⟨0, 6 * k + 1, 0, 0, E + 3 * k + 4⟩,
        ⟨6 * k + 1, E + 3 * k + 4, rfl, by omega, by omega⟩,
        main_trans_even k E⟩
    · -- b odd: b = 2k + 1
      subst hk
      obtain ⟨E, rfl⟩ : ∃ E, e = E + k + 2 := ⟨e - k - 2, by omega⟩
      refine ⟨⟨0, 6 * k + 4, 0, 0, E + 3 * k + 5⟩,
        ⟨6 * k + 4, E + 3 * k + 5, rfl, by omega, by omega⟩,
        main_trans_odd k E⟩
  · exact ⟨0, 2, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1294
