import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #49: [1/15, 7/3, 18/77, 5/7, 11979/2]

Vector representation:
```
 0 -1 -1  0  0
 0 -1  0  1  0
 1  2  0 -1 -1
 0  0  1 -1  0
-1  2  0  0  3
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_49

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+3⟩
  | _ => none

-- R4 repeated: transfer d to c
theorem d_to_c : ∀ k, ∀ a c d, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5,R1,R1 chain: drain c (two at a time) when c ≥ 2
theorem drain_pair : ∀ k, ∀ a c e, ⟨a + k, 0, c + 2 * k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3,R2,R2 chain: build phase
theorem build_phase : ∀ k, ∀ a d, ⟨a, 0, 0, d + 1, k⟩ [fm]⊢* ⟨a + k, 0, 0, d + 1 + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show (k + 1) = k + 1 from rfl]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Even transition: d = 2*q, q ≥ 0
-- From (a+q+1, 0, 0, 2*q, 0) with a+q+1 > q (i.e. a ≥ 0)
-- Phase 1: d_to_c -> (a+q+1, 0, 2*q, 0, 0)
-- Phase 2: drain_pair q rounds -> (a+1, 0, 0, 0, 3*q)
-- Phase 3: R5,R2,R2 -> (a, 0, 0, 2, 3*q+3)
-- Phase 4: build_phase 3*q+3 rounds -> (a+3*q+3, 0, 0, 3*q+5, 0)
-- Net: (a+q+1, 0, 0, 2*q, 0) -> (a+3*q+3, 0, 0, 3*q+5, 0)
theorem even_trans : ⟨a + q + 1, 0, 0, 2 * q, 0⟩ [fm]⊢⁺ ⟨a + 3 * q + 3, 0, 0, 3 * q + 5, 0⟩ := by
  -- Phase 1: d_to_c
  rw [show 2 * q = 0 + 2 * q from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * q) _ _ _)
  simp only [Nat.zero_add]
  -- Phase 2: drain_pair
  rw [show a + q + 1 = (a + 1) + q from by ring,
      show 2 * q = 0 + 2 * q from by ring]
  apply stepStar_stepPlus_stepPlus (drain_pair q _ _ _)
  simp only [Nat.zero_add]
  -- Phase 3: R5, R2, R2
  step fm; step fm; step fm
  -- Phase 4: build_phase
  apply stepStar_trans (build_phase (3 * q + 3) a 1)
  ring_nf; finish

-- Odd transition: d = 2*q+1, q ≥ 0
-- From (a+q+1, 0, 0, 2*q+1, 0) with a+q+1 > q (i.e. a ≥ 0)
-- Phase 1: d_to_c -> (a+q+1, 0, 2*q+1, 0, 0)
-- Phase 2: drain_pair q rounds -> (a+1, 0, 1, 0, 3*q)
-- Phase 3: R5,R1,R2 -> (a, 0, 0, 1, 3*q+3)
-- Phase 4: build_phase 3*q+3 rounds -> (a+3*q+3, 0, 0, 3*q+4, 0)
-- Net: (a+q+1, 0, 0, 2*q+1, 0) -> (a+3*q+3, 0, 0, 3*q+4, 0)
theorem odd_trans : ⟨a + q + 1, 0, 0, 2 * q + 1, 0⟩ [fm]⊢⁺ ⟨a + 3 * q + 3, 0, 0, 3 * q + 4, 0⟩ := by
  -- Phase 1: d_to_c
  rw [show 2 * q + 1 = 0 + (2 * q + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * q + 1) _ _ _)
  simp only [Nat.zero_add]
  -- Phase 2: drain_pair
  rw [show a + q + 1 = (a + 1) + q from by ring,
      show 2 * q + 1 = 1 + 2 * q from by ring]
  apply stepStar_stepPlus_stepPlus (drain_pair q _ _ _)
  -- Phase 3: R5, R1, R2
  step fm; step fm; step fm
  -- Phase 4: build_phase
  rw [show (0 : ℕ) + 3 * q + 3 = 3 * q + 3 from by ring]
  apply stepStar_trans (build_phase (3 * q + 3) a 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 5, 0⟩)
  · execute fm 12
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ 2 * a > d)
  · intro c ⟨a, d, hq, hineq⟩; subst hq
    rcases Nat.even_or_odd d with ⟨q, hq⟩ | ⟨q, hq⟩
    · -- d even: d = q + q = 2*q
      rw [show q + q = 2 * q from by ring] at hq; subst hq
      obtain ⟨m, rfl⟩ : ∃ m, a = m + q + 1 := ⟨a - q - 1, by omega⟩
      exact ⟨⟨m + 3 * q + 3, 0, 0, 3 * q + 5, 0⟩,
        ⟨m + 3 * q + 3, 3 * q + 5, rfl, by omega⟩, even_trans⟩
    · -- d odd: d = 2*q + 1
      subst hq
      obtain ⟨m, rfl⟩ : ∃ m, a = m + q + 1 := ⟨a - q - 1, by omega⟩
      exact ⟨⟨m + 3 * q + 3, 0, 0, 3 * q + 4, 0⟩,
        ⟨m + 3 * q + 3, 3 * q + 4, rfl, by omega⟩, odd_trans⟩
  · exact ⟨3, 5, rfl, by omega⟩

end Sz22_2003_unofficial_49
