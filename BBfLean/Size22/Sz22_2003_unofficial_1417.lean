import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1417: [7/15, 1210/3, 3/385, 5/11, 9/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  1  0  2
 0  1 -1 -1 -1
 0  0  1  0 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1417

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e+2⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R3-R2 spiral: (A, 0, 1, k, E+1) →* (A+k, 0, 1, 0, E+k+1)
theorem spiral : ∀ k, ∀ A E, ⟨A, 0, 1, k, E + 1⟩ [fm]⊢* ⟨A + k, 0, 1, 0, E + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  · step fm  -- R3: (A, 1, 0, k, E)
    step fm  -- R2: (A+1, 0, 1, k, E+2)
    rw [show E + 2 = (E + 1) + 1 from by ring]
    apply stepStar_trans (ih (A + 1) (E + 1))
    ring_nf; finish

-- R4 drain: (A, 0, C, 0, k) →* (A, 0, C+k, 0, 0)
theorem e_to_c : ∀ k, ∀ A C, ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · step fm  -- R4: (A, 0, C+1, 0, k)
    apply stepStar_trans (ih A (C + 1))
    ring_nf; finish

-- R5-R1-R1 chain: (A+k, 0, C+2*k, D, 0) →* (A, 0, C, D+2*k, 0)
theorem r5r1r1_chain : ∀ k, ∀ A C D, ⟨A + k, 0, C + 2 * k, D, 0⟩ [fm]⊢* ⟨A, 0, C, D + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C D
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k) + 2 from by ring]
    step fm  -- R5: (A+k, 2, C+2*k+2, D, 0)
    step fm  -- R1: (A+k, 1, C+2*k+1, D+1, 0)
    step fm  -- R1: (A+k, 0, C+2*k, D+2, 0)
    apply stepStar_trans (ih A C (D + 2))
    ring_nf; finish

-- Opening: (a+1, 0, 0, d+1, 0) →⁺ (a+2, 0, 1, d+1, 2)
theorem opening : ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 1, d + 1, 2⟩ := by
  step fm  -- R5: (a, 2, 0, d+1, 0)
  step fm  -- R2: (a+1, 1, 1, d+1, 2)
  step fm  -- R1: (a+1, 0, 0, d+2, 2)
  step fm  -- R4: (a+1, 0, 1, d+2, 1)
  step fm  -- R3: (a+1, 1, 0, d+1, 0)
  step fm  -- R2: (a+2, 0, 1, d+1, 2)
  finish

-- Odd-c remainder: (A+1, 0, 1, D, 0) → (A+1, 0, 1, D+1, 2)
theorem odd_rem : ⟨A + 1, 0, 1, D, 0⟩ [fm]⊢⁺ ⟨A + 1, 0, 1, D + 1, 2⟩ := by
  step fm  -- R5: (A, 2, 1, D, 0)
  step fm  -- R1: (A, 1, 0, D+1, 0)
  step fm  -- R2: (A+1, 0, 1, D+1, 2)
  finish

-- Main transition for even d:
-- (a, 0, 0, 2*m, 0) ⊢⁺ (a + 2*m, 0, 0, 2*m + 6, 0)
-- with a >= 1, m >= 1.
-- Phases: opening → spiral → e_to_c → r5r1r1(odd) → odd_rem → spiral → e_to_c → r5r1r1(even)
theorem main_trans (a m : ℕ) :
    ⟨a + 1, 0, 0, 2 * (m + 1), 0⟩ [fm]⊢⁺
    ⟨a + 2 * m + 3, 0, 0, 2 * m + 8, 0⟩ := by
  -- Phase 1: opening
  have h1 : ⟨a + 1, 0, 0, 2 * (m + 1), 0⟩ [fm]⊢⁺
      ⟨a + 2, 0, 1, 2 * (m + 1), 2⟩ := by
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 from by ring]
    exact opening
  -- Phase 2a: spiral k=2*(m+1)
  have h2a : ⟨a + 2, 0, 1, 2 * (m + 1), 2⟩ [fm]⊢*
      ⟨a + 2 * m + 4, 0, 1, 0, 2 * m + 4⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (spiral (2 * (m + 1)) (a + 2) 1)
    ring_nf; finish
  -- Phase 3a: e_to_c
  have h3a : ⟨a + 2 * m + 4, 0, 1, 0, 2 * m + 4⟩ [fm]⊢*
      ⟨a + 2 * m + 4, 0, 2 * m + 5, 0, 0⟩ := by
    apply stepStar_trans (e_to_c (2 * m + 4) (a + 2 * m + 4) 1)
    ring_nf; finish
  -- Phase 4a: r5r1r1 with k=m+2, C=1 (2*m+5 = 1 + 2*(m+2))
  have h4a : ⟨a + 2 * m + 4, 0, 2 * m + 5, 0, 0⟩ [fm]⊢*
      ⟨a + m + 2, 0, 1, 2 * m + 4, 0⟩ := by
    rw [show a + 2 * m + 4 = (a + m + 2) + (m + 2) from by ring,
        show 2 * m + 5 = 1 + 2 * (m + 2) from by ring]
    apply stepStar_trans (r5r1r1_chain (m + 2) (a + m + 2) 1 0)
    ring_nf; finish
  -- Phase 5: odd_rem
  have h5 : ⟨a + m + 2, 0, 1, 2 * m + 4, 0⟩ [fm]⊢⁺
      ⟨a + m + 2, 0, 1, 2 * m + 5, 2⟩ := by
    rw [show a + m + 2 = (a + m + 1) + 1 from by ring]
    exact odd_rem
  -- Phase 2b: spiral k=2*m+5
  have h2b : ⟨a + m + 2, 0, 1, 2 * m + 5, 2⟩ [fm]⊢*
      ⟨a + 3 * m + 7, 0, 1, 0, 2 * m + 7⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (spiral (2 * m + 5) (a + m + 2) 1)
    ring_nf; finish
  -- Phase 3b: e_to_c
  have h3b : ⟨a + 3 * m + 7, 0, 1, 0, 2 * m + 7⟩ [fm]⊢*
      ⟨a + 3 * m + 7, 0, 2 * m + 8, 0, 0⟩ := by
    apply stepStar_trans (e_to_c (2 * m + 7) (a + 3 * m + 7) 1)
    ring_nf; finish
  -- Phase 4b: r5r1r1 with k=m+4, C=0 (2*m+8 = 0 + 2*(m+4))
  have h4b : ⟨a + 3 * m + 7, 0, 2 * m + 8, 0, 0⟩ [fm]⊢*
      ⟨a + 2 * m + 3, 0, 0, 2 * m + 8, 0⟩ := by
    rw [show a + 3 * m + 7 = (a + 2 * m + 3) + (m + 4) from by ring,
        show 2 * m + 8 = 0 + 2 * (m + 4) from by ring]
    apply stepStar_trans (r5r1r1_chain (m + 4) (a + 2 * m + 3) 0 0)
    ring_nf; finish
  -- Compose all phases
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2a (stepStar_trans h3a (stepStar_trans h4a
      (stepStar_trans (stepPlus_stepStar h5)
        (stepStar_trans h2b (stepStar_trans h3b h4b))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 6, 0⟩) (by execute fm 34)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * n * n + 3 * n + 1, 0, 0, 6 * n + 6, 0⟩) 0
  intro n; exact ⟨n + 1, by
    rw [show 3 * n * n + 3 * n + 1 = (3 * n * n + 3 * n) + 1 from by ring,
        show 6 * n + 6 = 2 * ((3 * n + 2) + 1) from by ring,
        show 3 * (n + 1) * (n + 1) + 3 * (n + 1) + 1 = (3 * n * n + 3 * n) + 2 * (3 * n + 2) + 3 from by ring,
        show 6 * (n + 1) + 6 = 2 * (3 * n + 2) + 8 from by ring]
    exact main_trans (3 * n * n + 3 * n) (3 * n + 2)⟩

end Sz22_2003_unofficial_1417
