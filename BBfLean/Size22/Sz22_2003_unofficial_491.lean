import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #491: [28/15, 3/22, 25/2, 11/7, 231/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_491

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
  | _ => none

-- R1/R2 chain: k rounds of (R1, R2)
-- After k rounds starting from (j, 1, C+k, j+1, E+k):
--   result is (j+k, 1, C, j+1+k, E)
theorem r1r2_rounds : ∀ k, ∀ j C E,
    (⟨j, 1, C+k, j+1, E+k⟩ : Q) [fm]⊢* ⟨j+k, 1, C, j+1+k, E⟩ := by
  intro k; induction' k with k h <;> intro j C E
  · exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm
  -- After R1,R2: state is (j+1, 1, C+k, j+1+1, E+k)
  -- IH gives: (j+1, 1, C+k, j+1+1, E+k) ⊢* (j+1+k, 1, C, j+1+1+k, E)
  -- Target: (j+1, 1, C+k, j+1+1, E+k) ⊢* (j+(k+1), 1, C, j+1+(k+1), E)
  -- j+1+k = j+(k+1) and j+1+1+k = j+1+(k+1) by omega
  have := h (j + 1) C E
  show (j + 1, 1, C + k, j + 1 + 1, E + k) [fm]⊢* (j + (k + 1), 1, C, j + 1 + (k + 1), E)
  rw [show j + (k + 1) = j + 1 + k from by ring,
      show j + 1 + (k + 1) = j + 1 + 1 + k from by ring]
  exact this

-- R3 chain: convert a to c
theorem r3_chain : ∀ k, ∀ c d,
    (⟨k, 0, c, d, 0⟩ : Q) [fm]⊢* ⟨0, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R4 chain: convert d to e
theorem r4_chain : ∀ k, ∀ c e,
    (⟨0, 0, c, k, e⟩ : Q) [fm]⊢* ⟨0, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show k + 1 = k + 1 from rfl]
  step fm
  rw [show e + (k + 1) = (e + 1) + k from by ring]
  exact h c (e + 1)

-- After R5 and the R1/R2 chain, we need to do 5 more steps and then R3+R4 chains.
-- This lemma handles the tail: from (e', 1, c'+3, e'+1, 2) onward
theorem tail_phase (c' e' : ℕ) :
    (⟨e', 1, c'+3, e'+1, 2⟩ : Q) [fm]⊢* ⟨0, 0, c'+2*e'+8, 0, e'+4⟩ := by
  -- R1: (e'+2, 0, c'+2, e'+2, 2)
  rw [show c' + 3 = (c' + 2) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  -- R2: (e'+1, 1, c'+2, e'+2, 1)
  step fm
  -- R1: (e'+3, 0, c'+1, e'+3, 1)
  rw [show c' + 2 = (c' + 1) + 1 from by ring]
  step fm
  -- R2: (e'+2, 1, c'+1, e'+3, 0)
  step fm
  -- R1: (e'+4, 0, c', e'+4, 0)
  rw [show c' + 1 = c' + 1 from rfl]
  step fm
  -- Now: (e'+4, 0, c', e'+4, 0) — but with Lean's representation
  -- R3 chain: e'+4 times
  apply stepStar_trans
  · rw [show e' + 1 + 1 + 2 = e' + 4 from by ring,
        show e' + 1 + 1 + 1 + 1 = e' + 4 from by ring]
    exact r3_chain (e' + 4) c' (e' + 4)
  -- R4 chain: e'+4 times
  rw [show c' + 2 * (e' + 4) = c' + 2 * e' + 8 from by ring]
  have h := r4_chain (e' + 4) (c' + 2 * e' + 8) 0
  rw [show (0 : ℕ) + (e' + 4) = e' + 4 from by ring] at h
  exact h

-- Full transition from canonical form
theorem full_trans (c' e' : ℕ) :
    (⟨0, 0, c' + e' + 4, 0, e' + 1⟩ : Q) [fm]⊢⁺ ⟨0, 0, c' + 2*e' + 8, 0, e' + 4⟩ := by
  -- R5
  rw [show c' + e' + 4 = (c' + e' + 3) + 1 from by ring]
  step fm
  -- State: (0, 1, c'+e'+3, 1, e'+1+1)
  -- R1/R2 chain: e' rounds (j=0, C=c'+3, E=2, k=e')
  apply stepStar_trans
  · rw [show c' + e' + 3 = (c' + 3) + e' from by ring,
        show e' + 1 + 1 = 2 + e' from by ring]
    exact r1r2_rounds e' 0 (c' + 3) 2
  -- State: (0+e', 1, c'+3, 0+1+e', 2) = (e', 1, c'+3, 1+e', 2)
  rw [show (0 : ℕ) + e' = e' from by ring,
      show (0 : ℕ) + 1 + e' = e' + 1 from by ring]
  exact tail_phase c' e'

theorem main_trans (c e : ℕ) (hc : c ≥ e + 3) (he : e ≥ 1) :
    (⟨0, 0, c, 0, e⟩ : Q) [fm]⊢⁺ ⟨0, 0, c + e + 3, 0, e + 3⟩ := by
  obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hc
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le he
  rw [show 1 + e' + 3 + c' = c' + e' + 4 from by ring,
      show 1 + e' = e' + 1 from by ring]
  have h := full_trans c' e'
  rw [show c' + 2 * e' + 8 = (c' + e' + 4) + (e' + 1) + 3 from by ring,
      show e' + 4 = (e' + 1) + 3 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 11, 0, 6⟩) (by execute fm 33)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c, 0, e⟩ ∧ c ≥ e + 3 ∧ e ≥ 1)
  · intro q ⟨c, e, hq, hc, he⟩
    subst hq
    exact ⟨⟨0, 0, c + e + 3, 0, e + 3⟩,
           ⟨c + e + 3, e + 3, rfl, by omega, by omega⟩,
           main_trans c e hc he⟩
  · exact ⟨11, 6, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_491
