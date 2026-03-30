import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #796: [35/6, 605/2, 4/77, 3/5, 4/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_796

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

-- Phase 1: Move c to b via R4. (0, b, c+k, 0, e) →* (0, b+k, c, 0, e)
theorem c_to_b : ∀ k, ⟨(0 : ℕ), b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- Phase 2: R1R1R3 chain. Each round: a stays 2, b -= 2, c += 2, d += 1, e -= 1.
-- (2, 2*k, C, D, E+k) →* (2, 0, C+2*k, D+k, E)
theorem r1r1r3_chain : ∀ k, ∀ C D E,
    ⟨(2 : ℕ), 2 * k, C, D, E + k⟩ [fm]⊢* ⟨2, 0, C + 2 * k, D + k, E⟩ := by
  intro k; induction' k with k ih <;> intro C D E
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    step fm  -- R1
    step fm  -- R1
    rw [show E + k + 1 = (E + k) + 1 from by ring]
    step fm  -- R3
    apply stepStar_trans (ih (C + 2) (D + 1) E)
    ring_nf; finish

-- Phase 3: R2R2R3 chain. Each round: c += 2, d -= 1, e += 3.
-- (2, 0, C, d, E) →* (2, 0, C+2*d, 0, E+3*d)
theorem r2r2r3_chain : ∀ d, ∀ C E,
    ⟨(2 : ℕ), 0, C, d, E⟩ [fm]⊢* ⟨2, 0, C + 2 * d, 0, E + 3 * d⟩ := by
  intro d; induction' d with d ih <;> intro C E
  · exists 0
  · step fm  -- R2
    step fm  -- R2
    rw [show E + 4 = (E + 3) + 1 from by ring]
    step fm  -- R3
    apply stepStar_trans (ih (C + 2) (E + 3))
    ring_nf; finish

-- Main transition: (0, 0, 2*(m+1), 0, m+e+2) →⁺ (0, 0, 4*m+6, 0, 3*m+e+7)
theorem main_trans (m e : ℕ) :
    ⟨(0 : ℕ), 0, 2 * (m + 1), 0, m + e + 2⟩ [fm]⊢⁺
    ⟨0, 0, 4 * m + 6, 0, 3 * m + e + 7⟩ := by
  -- Phase 1: c_to_b
  rw [show (2 * (m + 1) : ℕ) = 0 + 2 * (m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (c_to_b (2 * (m + 1)) (b := 0) (c := 0) (e := m + e + 2))
  -- Phase 2: R5 step
  rw [show (m + e + 2 : ℕ) = (m + e + 1) + 1 from by ring]
  step fm
  -- Clean up 0+ patterns
  simp only [Nat.zero_add]
  -- Phase 3: R1R1R3 chain
  rw [show (m + e + 1 : ℕ) = e + (m + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (m + 1) 0 0 e)
  -- Phase 4: R2R2R3 chain
  simp only [Nat.zero_add]
  apply stepStar_trans (r2r2r3_chain (m + 1) (2 * (m + 1)) e)
  -- Phase 5: Two R2 steps
  step fm
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2 * (1 + 1), 0, 1 + 3 + 2⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, e⟩ ↦ ⟨0, 0, 2 * (m + 1), 0, m + e + 2⟩) ⟨1, 3⟩
  intro ⟨m, e⟩; exact ⟨⟨2 * m + 2, m + e + 3⟩, by
    show ⟨(0 : ℕ), 0, 2 * (m + 1), 0, m + e + 2⟩ [fm]⊢⁺
      ⟨0, 0, 2 * (2 * m + 2 + 1), 0, (2 * m + 2) + (m + e + 3) + 2⟩
    rw [show 2 * (2 * m + 2 + 1) = 4 * m + 6 from by ring,
        show (2 * m + 2) + (m + e + 3) + 2 = 3 * m + e + 7 from by ring]
    exact main_trans m e⟩
