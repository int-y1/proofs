import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #892: [4/15, 147/22, 25/2, 11/7, 14/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  2 -1
-1  0  2  0  0
 0  0  0 -1  1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_892

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: (0, 0, c, d+k, e) →* (0, 0, c, d, e+k)
theorem d_to_e : ∀ k, ∀ d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show e + 1 = (e + 1) from rfl]
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- R3 repeated: (a+k, 0, c, d, 0) →* (a, 0, c+2*k, d, 0)
theorem a_to_c : ∀ k, ∀ a c, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2))
    ring_nf; finish

-- R2+R1 chain: (A+1, 0, (C+1)+k, D, k+1) →* (A+k+2, 0, C, D+2*k+2, 0)
theorem r2r1_chain : ∀ k, ∀ A C D, ⟨A + 1, 0, (C + 1) + k, D, k + 1⟩ [fm]⊢* ⟨A + k + 2, 0, C, D + 2 * k + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C D
  · step fm; step fm; finish
  · rw [show (C + 1) + (k + 1) = ((C + 1) + k) + 1 from by ring,
        show (k : ℕ) + 1 + 1 = (k + 1) + 1 from by ring]
    step fm  -- R2: (A, 1, (C+1+k)+1, D+2, k+1)
    step fm  -- R1: (A+2, 0, C+1+k, D+2, k+1)
    rw [show A + 2 = (A + 1) + 1 from by ring]
    apply stepStar_trans (ih (A + 1) C (D + 2))
    ring_nf; finish

-- Main transition: (0, 0, d+2, d, 0) →⁺ (0, 0, 2*d+3, 2*d+1, 0)
theorem main_trans : ∀ d, ⟨0, 0, d + 2, d, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * d + 3, 2 * d + 1, 0⟩ := by
  intro d; rcases d with _ | d
  · execute fm 2
  · -- d+1: (0, 0, d+3, d+1, 0) →⁺ (0, 0, 2*d+5, 2*d+3, 0)
    -- Phase 1: d_to_e
    apply stepStar_stepPlus_stepPlus
    · rw [show (d : ℕ) + 1 = 0 + (d + 1) from by ring]
      exact d_to_e (d + 1) 0 0
    -- Now at (0, 0, d+3, 0, d+1)
    -- Phase 2: R5
    rw [show (0 : ℕ) + (d + 1) = d + 1 from by ring]
    apply step_stepStar_stepPlus
    · rw [show d + 3 = (d + 2) + 1 from by ring]
      show fm ⟨0, 0, (d + 2) + 1, 0, d + 1⟩ = some ⟨1, 0, d + 2, 1, d + 1⟩
      simp [fm]
    -- Now at (1, 0, d+2, 1, d+1)
    -- Phase 3: R2+R1 chain
    apply stepStar_trans
    · rw [show d + 2 = (1 + 1) + d from by ring,
          show d + 1 = d + 1 from rfl]
      show ⟨0 + 1, 0, (1 + 1) + d, 1, d + 1⟩ [fm]⊢* ⟨0 + d + 2, 0, 1, 1 + 2 * d + 2, 0⟩
      exact r2r1_chain d 0 1 1
    -- Now at (d+2, 0, 1, 2*d+3, 0)
    -- Phase 4: a_to_c
    rw [show 0 + d + 2 = 0 + (d + 2) from by ring,
        show 1 + 2 * d + 2 = 2 * d + 3 from by ring]
    apply stepStar_trans (a_to_c (d + 2) 0 1 (d := 2 * d + 3))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, d + 2, d, 0⟩) 0
  intro d; exact ⟨2 * d + 1, main_trans d⟩
