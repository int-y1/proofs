import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1516: [7/15, 99/14, 4/3, 25/11, 21/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  1
 2 -1  0  0  0
 0  0  2  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1516

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: move e to c (doubled). (a, 0, c, 0, e+k) →* (a, 0, c+2*k, 0, e)
theorem e_to_c : ∀ k, ⟨a, (0:ℕ), c, (0:ℕ), e + k⟩ [fm]⊢* ⟨a, (0:ℕ), c + 2 * k, (0:ℕ), e⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 2))
    ring_nf; finish

-- R3 chain: move b to a (doubled). (a, b+k, 0, 0, e) →* (a+2*k, b, 0, 0, e)
theorem b_to_a : ∀ k, ⟨a, b + k, (0:ℕ), (0:ℕ), e⟩ [fm]⊢* ⟨a + 2 * k, b, (0:ℕ), (0:ℕ), e⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    apply stepStar_trans (ih (a := a) (b := b + 1))
    rw [show a + 2 * k = (a + 2 * k) from rfl]
    step fm
    ring_nf; finish

-- R2R1R1 chain: e rounds of (R2, R1, R1).
-- ⟨X+k, 0, C+2*k, Z+1, W⟩ →* ⟨X, 0, C, Z+k+1, W+k⟩
theorem r2r1r1_chain : ∀ k, ∀ X C Z W, ⟨X + k, (0:ℕ), C + 2 * k, Z + 1, W⟩ [fm]⊢* ⟨X, (0:ℕ), C, Z + k + 1, W + k⟩ := by
  intro k; induction' k with k ih <;> intro X C Z W
  · exists 0
  · rw [show X + (k + 1) = (X + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k) + 2 from by ring]
    step fm  -- R2: (X+k, 2, C+2*k+2, Z, W+1)
    step fm  -- R1: (X+k, 1, C+2*k+1, Z+1, W+1)
    step fm  -- R1: (X+k, 0, C+2*k, Z+2, W+1)
    rw [show Z + 2 = (Z + 1) + 1 from by ring]
    apply stepStar_trans (ih X C (Z + 1) (W + 1))
    ring_nf; finish

-- R2 drain: when c=0, b>=1, drain d via R2. (A, B, 0, D+k, E) →* (A-k, B+2*k, 0, D, E+k)
-- Needs A >= k, encoded as A = X + k.
theorem r2_drain : ∀ k, ∀ X B D E, ⟨X + k, B, (0:ℕ), D + k, E⟩ [fm]⊢* ⟨X, B + 2 * k, (0:ℕ), D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro X B D E
  · exists 0
  · rw [show X + (k + 1) = (X + k) + 1 from by ring,
        show D + (k + 1) = (D + k) + 1 from by ring]
    step fm  -- R2: (X+k, B+2, 0, D+k, E+1)
    apply stepStar_trans (ih X (B + 2) D (E + 1))
    ring_nf; finish

-- Main transition: (m+2*e+4, 0, 0, 0, e+1) →⁺ (m+4*e+10, 0, 0, 0, 2*e+3)
theorem main_transition (m e : ℕ) :
    ⟨m + 2 * e + 4, (0:ℕ), (0:ℕ), (0:ℕ), e + 1⟩ [fm]⊢⁺
    ⟨m + 4 * e + 10, (0:ℕ), (0:ℕ), (0:ℕ), 2 * e + 3⟩ := by
  -- Phase 1: R4 chain, e+1 steps: (a, 0, 0, 0, e+1) → (a, 0, 2e+2, 0, 0)
  rw [show (e : ℕ) + 1 = 0 + (e + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (e + 1) (a := m + 2 * e + 4) (c := 0) (e := 0))
  rw [show (0 : ℕ) + 2 * (e + 1) = 2 * e + 2 from by ring]
  -- State: (m+2e+4, 0, 2e+2, 0, 0)
  -- Phase 2: R5
  rw [show m + 2 * e + 4 = (m + 2 * e + 3) + 1 from by ring]
  step fm  -- R5: (m+2e+3, 1, 2e+2, 1, 0)
  -- Phase 3: R1
  rw [show (2 : ℕ) * e + 2 = (2 * e + 1) + 1 from by ring]
  step fm  -- R1: (m+2e+3, 0, 2e+1, 2, 0)
  -- State: (m+2e+3, 0, 2e+1, 2, 0)
  -- Phase 4: R2R1R1 chain, e rounds
  -- ⟨X+k, 0, C+2*k, Z+1, W⟩ →* ⟨X, 0, C, Z+k+1, W+k⟩
  -- Set X+k = m+2e+3, C+2k = 2e+1, Z+1 = 2, W = 0, k = e
  -- So X = m+e+3, C = 1, Z = 1
  rw [show m + 2 * e + 3 = (m + e + 3) + e from by ring,
      show (2 : ℕ) * e + 1 = 1 + 2 * e from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r2r1r1_chain e (m + e + 3) 1 1 0)
  rw [show (1 : ℕ) + e + 1 = e + 2 from by ring,
      show (0 : ℕ) + e = e from by ring]
  -- State: (m+e+3, 0, 1, e+2, e)
  -- Phase 5: Partial round R2 + R1
  rw [show m + e + 3 = (m + e + 2) + 1 from by ring,
      show e + 2 = (e + 1) + 1 from by ring]
  step fm  -- R2: (m+e+2, 2, 1, e+1, e+1)
  step fm  -- R1: (m+e+2, 1, 0, e+2, e+1)
  -- State: (m+e+2, 1, 0, e+1+1, e+1)
  -- Phase 6: R2 drain, e+2 steps
  have h6 : ⟨m + (e + 2), 1, (0:ℕ), 0 + (e + 2), e + 1⟩ [fm]⊢*
             ⟨m, 1 + 2 * (e + 2), (0:ℕ), (0:ℕ), e + 1 + (e + 2)⟩ :=
    r2_drain (e + 2) m 1 0 (e + 1)
  simp only [Nat.zero_add] at h6
  rw [show m + e + 2 = m + (e + 2) from by ring,
      show e + 1 + 1 = e + 2 from by ring]
  apply stepStar_trans h6
  rw [show (1 : ℕ) + 2 * (e + 2) = 2 * e + 5 from by ring,
      show e + 1 + (e + 2) = 2 * e + 3 from by ring]
  -- State: (m, 2e+5, 0, 0, 2e+3)
  -- Phase 7: R3 chain (b_to_a)
  rw [show (2 : ℕ) * e + 5 = 0 + (2 * e + 5) from by ring]
  apply stepStar_trans (b_to_a (2 * e + 5) (a := m) (b := 0) (e := 2 * e + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, e⟩ ↦ ⟨m + 2 * e + 4, 0, 0, 0, e + 1⟩) ⟨1, 0⟩
  intro ⟨m, e⟩; exists ⟨m + 2, 2 * e + 2⟩
  show ⟨m + 2 * e + 4, (0:ℕ), (0:ℕ), (0:ℕ), e + 1⟩ [fm]⊢⁺
       ⟨(m + 2) + 2 * (2 * e + 2) + 4, (0:ℕ), (0:ℕ), (0:ℕ), (2 * e + 2) + 1⟩
  have h := main_transition m e
  rw [show m + 4 * e + 10 = (m + 2) + 2 * (2 * e + 2) + 4 from by ring,
      show 2 * e + 3 = (2 * e + 2) + 1 from by ring] at h
  exact h

end Sz22_2003_unofficial_1516
