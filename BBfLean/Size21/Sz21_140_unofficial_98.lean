import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #98: [63/10, 5/33, 2/3, 11/7, 105/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  0 -1
 1 -1  0  0  0
 0  0  0 -1  1
-1  1  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_98

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d+1, e⟩
  | _ => none

-- Phase 1: R4 repeated: d → e (when b=0, c=0)
-- Implicit params order: a, d, k, e
theorem d_to_e {a d k e : ℕ} : ⟨a, 0, 0, d+k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+k⟩ := by
  have many_step : ∀ k d e, ⟨a, 0, 0, d+k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k d e

-- Phase 2: R3 repeated: b → a (when c=0, e=0)
-- Implicit params order: a, b, k, d
theorem b_to_a {a b k d : ℕ} : ⟨a, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+k, b, 0, d, 0⟩ := by
  have many_step : ∀ k a b, ⟨a, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+k, b, 0, d, 0⟩ := by
    intro k; induction' k with k h <;> intro a b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a b

-- Phase 3: R2 repeated: b,e → c (when a=0)
-- Implicit params order: b, k, c, d
theorem r2_drain {b k c d : ℕ} : ⟨0, b+k, c, d, k⟩ [fm]⊢* ⟨0, b, c+k, d, 0⟩ := by
  have many_step : ∀ k b c, ⟨0, b+k, c, d, k⟩ [fm]⊢* ⟨0, b, c+k, d, 0⟩ := by
    intro k; induction' k with k h <;> intro b c
    · exists 0
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b c

-- Interleaved R2,R1 rounds: k rounds
-- From (k, B+1, 0, D, E+k) → (0, B+k+1, 0, D+k, E)
theorem r2r1_rounds : ∀ k, ∀ B D E, ⟨k, B+1, 0, D, E+k⟩ [fm]⊢* ⟨0, B+k+1, 0, D+k, E⟩ := by
  intro k; induction' k with k h <;> intro B D E
  · exists 0
  rw [show E + (k + 1) = (E + k) + 1 from by ring]
  step fm
  step fm
  have h2 := h (B + 1) (D + 1) E
  rw [show B + 2 = (B + 1) + 1 from by ring]
  refine stepStar_trans h2 ?_
  ring_nf; finish

-- R3,R1 chain: k rounds from (0, B+1, k, D, 0) → (0, B+k+1, 0, D+k, 0)
theorem r3r1_chain : ∀ k, ∀ B D, ⟨0, B+1, k, D, 0⟩ [fm]⊢* ⟨0, B+k+1, 0, D+k, 0⟩ := by
  intro k; induction' k with k h <;> intro B D
  · exists 0
  step fm
  step fm
  have h2 := h (B + 1) (D + 1)
  rw [show B + 2 = (B + 1) + 1 from by ring]
  refine stepStar_trans h2 ?_
  ring_nf; finish

-- Main transition: C(n) = (n+2, 0, 0, 2*n+2, 0) ⊢⁺ C(n+1) = (n+3, 0, 0, 2*n+4, 0)
theorem main_trans : ⟨n+2, 0, 0, 2*n+2, 0⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 2*n+4, 0⟩ := by
  -- Phase 1: d_to_e: (n+2, 0, 0, 0+(2*n+2), 0) →* (n+2, 0, 0, 0, 0+(2*n+2))
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n+2, 0, 0, 0, 2*n+2⟩)
  · have h := @d_to_e (n+2) 0 (2*n+2) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5: (n+2, 0, 0, 0, 2*n+2) → (n+1, 1, 1, 1, 2*n+2)
  apply step_stepStar_stepPlus (c₂ := ⟨n+1, 1, 1, 1, 2*n+2⟩)
  · show fm ⟨(n+1)+1, 0, 0, 0, 2*n+2⟩ = some ⟨n+1, 0+1, 0+1, 0+1, 2*n+2⟩
    simp [fm]
  -- Phase 3: R1: (n+1, 1, 1, 1, 2*n+2) → (n, 3, 0, 2, 2*n+2)
  apply stepStar_trans (c₂ := ⟨n, 3, 0, 2, 2*n+2⟩)
  · have h1 : fm ⟨n+1, 1, 1, 1, 2*n+2⟩ = some ⟨n, 3, 0, 2, 2*n+2⟩ := by
      show fm ⟨(n)+1, 1, (0)+1, 1, 2*n+2⟩ = some ⟨n, 1+2, 0, 1+1, 2*n+2⟩
      simp [fm]
    exact step_stepStar h1
  -- Phase 4: R2,R1 rounds: n rounds from (n, 3, 0, 2, (n+2)+n) → (0, n+3, 0, n+2, n+2)
  apply stepStar_trans (c₂ := ⟨0, n+3, 0, n+2, n+2⟩)
  · have h := r2r1_rounds n 2 2 (n+2)
    rw [show (2 : ℕ) + 1 = 3 from rfl,
        show (n : ℕ) + 2 + n = 2 * n + 2 from by ring,
        show (2 : ℕ) + n + 1 = n + 3 from by ring,
        show (2 : ℕ) + n = n + 2 from by ring] at h
    exact h
  -- Phase 5: R2 drain: (n+2) rounds from (0, 1+(n+2), 0, n+2, n+2) → (0, 1, (n+2), n+2, 0)
  apply stepStar_trans (c₂ := ⟨0, 1, n+2, n+2, 0⟩)
  · have h := @r2_drain 1 (n+2) 0 (n+2)
    simp only [Nat.zero_add] at h
    rw [show (1 : ℕ) + (n + 2) = n + 3 from by ring] at h
    exact h
  -- Phase 6: R3,R1 chain: (n+2) rounds from (0, 1, n+2, n+2, 0) → (0, n+3, 0, 2*n+4, 0)
  apply stepStar_trans (c₂ := ⟨0, n+3, 0, 2*n+4, 0⟩)
  · have h := r3r1_chain (n+2) 0 (n+2)
    rw [show (0 : ℕ) + 1 = 1 from rfl,
        show (0 : ℕ) + (n + 2) + 1 = n + 3 from by ring,
        show (n : ℕ) + 2 + (n + 2) = 2 * n + 4 from by ring] at h
    exact h
  -- Phase 7: b_to_a: (0, 0+(n+3), 0, 2*n+4, 0) → (0+(n+3), 0, 0, 2*n+4, 0)
  have h := @b_to_a 0 0 (n+3) (2*n+4)
  simp only [Nat.zero_add] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  -- c₀ = (1, 0, 0, 0, 0) reaches C(0) = (2, 0, 0, 2, 0) in 5 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+2, 0, 0, 2*n+2, 0⟩) 0
  intro n; exact ⟨n+1, main_trans⟩

end Sz21_140_unofficial_98
