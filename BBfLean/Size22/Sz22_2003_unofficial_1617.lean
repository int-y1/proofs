import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1617: [77/15, 2/3, 9/14, 5/11, 1617/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  0  0
-1  2  0 -1  0
 0  0  1  0 -1
-1  1  0  2  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1617

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e+1⟩
  | _ => none

-- R4 chain: transfer e to c
theorem e_to_c : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · rw [show C + (k + 1) = (C + 1) + k from by ring]
    step fm; exact ih A (C + 1)

-- (R3, R2, R2) chain: each round a+=1, d-=1
theorem r3r2r2_chain : ∀ k, ∀ A E,
    ⟨A + 1, 0, 0, k + 1, E⟩ [fm]⊢* ⟨A + k + 2, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show A + (k + 1) + 2 = (A + 1) + k + 2 from by ring,
        show A + 1 + 1 = (A + 1) + 1 from by ring]
    exact ih (A + 1) E

-- Even drain: k rounds of (R3,R1,R1) for c=2k
theorem drain_even : ∀ k, ∀ A D E,
    ⟨A + k, 0, 2 * k, D + 1, E⟩ [fm]⊢* ⟨A, 0, 0, D + k + 1, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · simp; exists 0
  · rw [show 2 * (k + 1) = (2 * k) + 1 + 1 from by ring,
        show A + (k + 1) = (A + k) + 1 from by ring]
    step fm; step fm; step fm
    have goal := ih A (D + 1) (E + 2)
    rw [show D + 1 + k + 1 = D + (k + 1) + 1 from by ring,
        show E + 2 + 2 * k = E + 2 * (k + 1) from by ring] at goal
    convert goal using 2

-- Odd drain: k rounds of (R3,R1,R1) then (R3,R1,R2) for c=2k+1
theorem drain_odd : ∀ k, ∀ A D E,
    ⟨A + k + 1, 0, 2 * k + 1, D + 1, E⟩ [fm]⊢* ⟨A + 1, 0, 0, D + k + 1, E + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · -- k=0, C=1: (R3, R1, R2)
    step fm; step fm; step fm; ring_nf; finish
  · -- k+1, C=2(k+1)+1=2k+3: (R3,R1,R1) then recurse with k
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring,
        show A + (k + 1) + 1 = (A + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    have goal := ih A (D + 1) (E + 2)
    rw [show D + 1 + k + 1 = D + (k + 1) + 1 from by ring,
        show E + 2 + 2 * k + 1 = E + 2 * (k + 1) + 1 from by ring] at goal
    convert goal using 2

-- Main transition for even n=2k:
-- (4k+3, 0, 0, 0, 2k+1) ⊢⁺ (4k+5, 0, 0, 0, 2k+2)
theorem main_trans_even (k : ℕ) :
    ⟨4 * k + 3, 0, 0, 0, 2 * k + 1⟩ [fm]⊢⁺ ⟨4 * k + 5, 0, 0, 0, 2 * k + 2⟩ := by
  -- Phase 1: R4 x (2k+1)
  have p1 : ⟨4 * k + 3, 0, 0, 0, 2 * k + 1⟩ [fm]⊢* ⟨4 * k + 3, 0, 2 * k + 1, 0, 0⟩ := by
    have h := e_to_c (2 * k + 1) (4 * k + 3) 0; simpa using h
  -- Phase 2: R5, R1
  have p2 : ⟨4 * k + 3, 0, 2 * k + 1, 0, 0⟩ [fm]⊢* ⟨4 * k + 2, 0, 2 * k, 3, 2⟩ := by
    rw [show 4 * k + 3 = (4 * k + 2) + 1 from by ring,
        show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm; ring_nf; finish
  -- Phase 3: drain_even k
  -- (4k+2, 0, 2k, 3, 2) = (3k+2+k, 0, 2k, 2+1, 2) -> (3k+2, 0, 0, k+3, 2k+2)
  have p3 : ⟨4 * k + 2, 0, 2 * k, 3, 2⟩ [fm]⊢* ⟨3 * k + 2, 0, 0, k + 3, 2 * k + 2⟩ := by
    rw [show 4 * k + 2 = (3 * k + 2) + k from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    have h := drain_even k (3 * k + 2) 2 2
    rw [show 2 + k + 1 = k + 3 from by ring,
        show 2 + 2 * k = 2 * k + 2 from by ring] at h
    exact h
  -- Phase 4: r3r2r2 chain (k+2 rounds)
  have p4 : ⟨3 * k + 2, 0, 0, k + 3, 2 * k + 2⟩ [fm]⊢* ⟨4 * k + 5, 0, 0, 0, 2 * k + 2⟩ := by
    rw [show k + 3 = (k + 2) + 1 from by ring,
        show 3 * k + 2 = (3 * k + 1) + 1 from by ring]
    have h := r3r2r2_chain (k + 2) (3 * k + 1) (2 * k + 2)
    rw [show 3 * k + 1 + (k + 2) + 2 = 4 * k + 5 from by ring] at h
    exact h
  have p_all := stepStar_trans (stepStar_trans (stepStar_trans p1 p2) p3) p4
  exact stepStar_stepPlus p_all (by simp [Q])

-- Main transition for odd n=2k+1:
-- (4k+5, 0, 0, 0, 2k+2) ⊢⁺ (4k+7, 0, 0, 0, 2k+3)
theorem main_trans_odd (k : ℕ) :
    ⟨4 * k + 5, 0, 0, 0, 2 * k + 2⟩ [fm]⊢⁺ ⟨4 * k + 7, 0, 0, 0, 2 * k + 3⟩ := by
  -- Phase 1: R4 x (2k+2)
  have p1 : ⟨4 * k + 5, 0, 0, 0, 2 * k + 2⟩ [fm]⊢* ⟨4 * k + 5, 0, 2 * k + 2, 0, 0⟩ := by
    have h := e_to_c (2 * k + 2) (4 * k + 5) 0; simpa using h
  -- Phase 2: R5, R1
  have p2 : ⟨4 * k + 5, 0, 2 * k + 2, 0, 0⟩ [fm]⊢* ⟨4 * k + 4, 0, 2 * k + 1, 3, 2⟩ := by
    rw [show 4 * k + 5 = (4 * k + 4) + 1 from by ring,
        show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm; ring_nf; finish
  -- Phase 3: drain_odd k
  -- (4k+4, 0, 2k+1, 3, 2) = (3k+3+k+1, 0, 2k+1, 2+1, 2)
  -- drain_odd k A D E: (A+k+1, 0, 2k+1, D+1, E) -> (A+1, 0, 0, D+k+1, E+2k+1)
  -- We need A+k+1 = 4k+4, so A = 3k+3
  -- D+1 = 3, so D = 2
  -- Result: (3k+4, 0, 0, k+3, 2k+3)
  have p3 : ⟨4 * k + 4, 0, 2 * k + 1, 3, 2⟩ [fm]⊢* ⟨3 * k + 4, 0, 0, k + 3, 2 * k + 3⟩ := by
    rw [show 4 * k + 4 = (3 * k + 3) + k + 1 from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    have h := drain_odd k (3 * k + 3) 2 2
    rw [show 3 * k + 3 + 1 = 3 * k + 4 from by ring,
        show 2 + k + 1 = k + 3 from by ring,
        show 2 + 2 * k + 1 = 2 * k + 3 from by ring] at h
    exact h
  -- Phase 4: r3r2r2 chain (k+2 rounds)
  have p4 : ⟨3 * k + 4, 0, 0, k + 3, 2 * k + 3⟩ [fm]⊢* ⟨4 * k + 7, 0, 0, 0, 2 * k + 3⟩ := by
    rw [show k + 3 = (k + 2) + 1 from by ring,
        show 3 * k + 4 = (3 * k + 3) + 1 from by ring]
    have h := r3r2r2_chain (k + 2) (3 * k + 3) (2 * k + 3)
    rw [show 3 * k + 3 + (k + 2) + 2 = 4 * k + 7 from by ring] at h
    exact h
  have p_all := stepStar_trans (stepStar_trans (stepStar_trans p1 p2) p3) p4
  exact stepStar_stepPlus p_all (by simp [Q])

-- Combined two-step transition: (4k+3, 0, 0, 0, 2k+1) ⊢⁺ (4k+7, 0, 0, 0, 2k+3)
theorem main_trans (k : ℕ) :
    ⟨4 * k + 3, 0, 0, 0, 2 * k + 1⟩ [fm]⊢⁺ ⟨4 * k + 7, 0, 0, 0, 2 * k + 3⟩ := by
  exact stepPlus_stepStar_stepPlus (main_trans_even k) (stepPlus_stepStar (main_trans_odd k))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨4 * k + 3, 0, 0, 0, 2 * k + 1⟩) 0
  intro k; refine ⟨k + 1, ?_⟩
  rw [show 4 * (k + 1) + 3 = 4 * k + 7 from by ring,
      show 2 * (k + 1) + 1 = 2 * k + 3 from by ring]
  exact main_trans k

end Sz22_2003_unofficial_1617
