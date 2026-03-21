import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #115: [77/15, 28/3, 9/22, 5/7, 3/2]

Vector representation:
```
 0 -1 -1  1  1
 2 -1  0  1  0
-1  2  0  0 -1
 0  0  1 -1  0
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_115

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: d → c
theorem d_to_c : ∀ k c d, ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- Inner round: R3, R1, R1
theorem inner_round : ⟨A+1, 0, C+2, D, E+1⟩ [fm]⊢* ⟨A, 0, C, D+2, E+2⟩ := by
  step fm
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm; step fm; finish

-- Inner loop: k rounds
theorem inner_loop : ∀ k, ∀ A C D E, ⟨A+k, 0, C+2*k, D, E+1⟩ [fm]⊢* ⟨A, 0, C, D+2*k, E+k+1⟩ := by
  intro k; induction' k with k h <;> intro A C D E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show C + 2 * (k + 1) = (C + 2 * k) + 2 from by ring]
  apply stepStar_trans (@inner_round (A + k) (C + 2 * k) D E)
  rw [show E + 2 = (E + 1) + 1 from by ring]
  apply stepStar_trans (h A C (D + 2) (E + 1))
  ring_nf; finish

-- Phase B round: R3, R2, R2
theorem phase_b_round : ⟨A+1, 0, 0, D, E+1⟩ [fm]⊢* ⟨A+4, 0, 0, D+2, E⟩ := by
  -- R3: (A+1, 0, 0, D, E+1) → (A, 2, 0, D, E)
  step fm
  -- R2: (A, 2, 0, D, E) → (A+2, 1, 0, D+1, E)
  step fm
  -- R2: (A+2, 1, 0, D+1, E) → (A+4, 0, 0, D+2, E)
  -- Need to rewrite A+2 as (A+2)+1-1... actually the issue is matching patterns
  -- The state should be (A+2, 1, 0, D+1, E) and R2 matches (a, b+1, c, d, e)
  -- giving (a+2, b, c, d+1, e) = (A+4, 0, 0, D+2, E)
  step fm; ring_nf; finish

-- Phase B chain: k rounds
theorem phase_b_chain : ∀ k, ∀ A D, ⟨A+k, 0, 0, D, k⟩ [fm]⊢* ⟨A+4*k, 0, 0, D+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro A D
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring]
  apply stepStar_trans (@phase_b_round (A + k) D k)
  rw [show A + k + 4 = (A + 4) + k from by ring]
  apply stepStar_trans (h (A + 4) (D + 2))
  ring_nf; finish

-- Bridge for even d: R3, R1, R2
theorem bridge_even (K : ℕ) : ⟨K+2, 0, 1, 2*K+1, K+1⟩ [fm]⊢* ⟨K+3, 0, 0, 2*K+3, K+1⟩ := by
  rw [show K + 2 = (K + 1) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm
  ring_nf; finish

-- Odd d: d = 2K+1
theorem complex_odd (K : ℕ) : ⟨2*K+2, 0, 2*K+1, 0, 0⟩ [fm]⊢⁺ ⟨4*K+4, 0, 0, 4*K+3, 0⟩ := by
  rw [show 2 * K + 2 = (2 * K + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(2 * K + 1) + 1, 0, 2 * K + 1, 0, 0⟩ = some ⟨2 * K + 1, 1, 2 * K + 1, 0, 0⟩
    simp [fm]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨2 * K + 1, 0 + 1, (2 * K) + 1, 0, 0⟩ = some ⟨2 * K + 1, 0, 2 * K, 1, 1⟩
    simp [fm]
  apply stepStar_trans
  · rw [show 2 * K + 1 = (K + 1) + K from by ring,
        show 2 * K = 0 + 2 * K from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    exact inner_loop K (K + 1) 0 1 0
  rw [show K + 1 = 0 + (K + 1) from by ring,
      show 1 + 2 * K = 2 * K + 1 from by ring,
      show 0 + K + 1 = K + 1 from by ring]
  apply stepStar_trans (phase_b_chain (K + 1) 0 (2 * K + 1))
  ring_nf; finish

-- Even d: d = 2K+2
theorem complex_even (K : ℕ) : ⟨2*K+3, 0, 2*K+2, 0, 0⟩ [fm]⊢⁺ ⟨4*K+6, 0, 0, 4*K+5, 0⟩ := by
  rw [show 2 * K + 3 = (2 * K + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(2 * K + 2) + 1, 0, 2 * K + 2, 0, 0⟩ = some ⟨2 * K + 2, 1, 2 * K + 2, 0, 0⟩
    simp [fm]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨2 * K + 2, 0 + 1, (2 * K + 1) + 1, 0, 0⟩ = some ⟨2 * K + 2, 0, 2 * K + 1, 1, 1⟩
    simp [fm]
  apply stepStar_trans
  · rw [show 2 * K + 2 = (K + 2) + K from by ring,
        show 2 * K + 1 = 1 + 2 * K from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    exact inner_loop K (K + 2) 1 1 0
  apply stepStar_trans
  · rw [show 1 + 2 * K = 2 * K + 1 from by ring,
        show 0 + K + 1 = K + 1 from by ring]
    exact bridge_even K
  rw [show K + 3 = 2 + (K + 1) from by ring]
  apply stepStar_trans (phase_b_chain (K + 1) 2 (2 * K + 3))
  ring_nf; finish

-- Main transition
theorem main_trans (d : ℕ) : ⟨d+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2*d+2, 0, 0, 2*d+1, 0⟩ := by
  rcases d with _ | d
  · -- d = 0
    step fm; step fm; finish
  -- d ≥ 1: R4 chain + complex phase
  apply stepStar_stepPlus_stepPlus
  · -- R4 chain: (d+2, 0, 0, d+1, 0) →* (d+2, 0, d+1, 0, 0)
    have h := d_to_c (d + 1) 0 0 (a := d + 2)
    simp only [Nat.zero_add] at h
    exact h
  -- Split on parity of d
  rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- d = K+K, d+1 = 2K+1 (odd)
    subst hK
    have h := complex_odd K
    -- Massage to match goal
    convert h using 2; ring_nf
  · -- d = 2K+1, d+1 = 2K+2 (even)
    subst hK
    have h := complex_even K
    convert h using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨d+1, 0, 0, d, 0⟩) 0
  intro d; exact ⟨2*d+1, main_trans d⟩
