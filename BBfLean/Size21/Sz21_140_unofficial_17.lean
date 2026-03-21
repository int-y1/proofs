import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #17: [2/15, 99/14, 25/2, 7/11, 14/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_17

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- consume_pairs: R2,R1,R1 chain
theorem consume_pairs : ∀ k, ∀ A C D E, ⟨A+1, 0, C+2*k, D+k, E⟩ [fm]⊢* ⟨A+1+k, 0, C, D, E+k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · exists 0
  rw [show C + 2 * (k + 1) = (C + 2 * k + 1) + 1 from by ring,
      show D + (k + 1) = (D + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (A + 1) C D (E + 1))
  ring_nf; finish

-- r2_chain: drain d, producing b and e
theorem r2_chain : ∀ k, ∀ A B E, ⟨A+k, B, 0, k, E⟩ [fm]⊢* ⟨A, B+2*k, 0, 0, E+k⟩ := by
  intro k; induction' k with k ih <;> intro A B E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih A (B + 2) (E + 1))
  ring_nf; finish

-- r3r1r1_chain: drain b by pairs
theorem r3r1r1_chain : ∀ k, ∀ A B E, ⟨A+1, B+2*k, 0, 0, E⟩ [fm]⊢* ⟨A+1+k, B, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A B E
  · exists 0
  rw [show B + 2 * (k + 1) = (B + 2 * k + 1) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (A + 1) B E)
  ring_nf; finish

-- r3_chain: drain a to c
theorem r3_chain : ∀ k, ∀ A C E, ⟨A+k, 0, C, 0, E⟩ [fm]⊢* ⟨A, 0, C+2*k, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A C E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih A (C + 2) E)
  ring_nf; finish

-- r4_chain: drain e to d
theorem r4_chain : ∀ k, ∀ C D, ⟨0, 0, C, D, k⟩ [fm]⊢* ⟨0, 0, C, D+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro C D
  · exists 0
  step fm
  apply stepStar_trans (ih C (D + 1))
  ring_nf; finish

-- odd_b_step: handle remainder when b is odd
theorem odd_b_step (A E : ℕ) : ⟨A+1, 1, 0, 0, E⟩ [fm]⊢* ⟨A+1, 0, 1, 0, E⟩ := by
  step fm; step fm; finish

-- Phase 1 even
theorem phase1_even (k : ℕ) : ⟨1, 0, 2*k, 2*k, 0⟩ [fm]⊢* ⟨1, 2*k, 0, 0, 2*k⟩ := by
  apply stepStar_trans (c₂ := ⟨1+k, 0, 0, k, k⟩)
  · have h := consume_pairs k 0 0 k 0
    rw [show (0 : ℕ) + 1 = 1 from rfl, show (0 : ℕ) + 2 * k = 2 * k from by omega,
        show (0 : ℕ) + 1 + k = 1 + k from by omega, show (0 : ℕ) + k = k from by omega] at h
    rw [show (2 : ℕ) * k = 2 * k from rfl, show k + k = 2 * k from by ring] at *
    exact h
  have h := r2_chain k 1 0 k
  rw [show (0 : ℕ) + 2 * k = 2 * k from by omega, show k + k = 2 * k from by ring] at h
  exact h

-- Phase 1 odd
theorem phase1_odd_base : ⟨1, 0, 1, 1, 0⟩ [fm]⊢* ⟨1, 1, 0, 0, 1⟩ := by
  execute fm 2

theorem phase1_odd (k : ℕ) : ⟨1, 0, 2*k+1, 2*k+1, 0⟩ [fm]⊢* ⟨1, 2*k+1, 0, 0, 2*k+1⟩ := by
  rcases k with _ | k
  · exact phase1_odd_base
  · apply stepStar_trans (c₂ := ⟨0+1+(k+1), 0, 1, (1+k)+1, 0+(k+1)⟩)
    · have h := consume_pairs (k+1) 0 1 ((1+k)+1) 0
      rw [show (0 : ℕ) + 1 = 1 from rfl,
          show 1 + 2 * (k + 1) = 2 * k + 3 from by ring,
          show ((1 : ℕ) + k) + 1 + (k + 1) = 2 * k + 3 from by ring] at h
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by ring]; exact h
    apply stepStar_trans (c₂ := ⟨0+1+(k+1), 1, 0, 1+k, 0+(k+1)+1⟩)
    · step fm; step fm; finish
    have h := r2_chain (1+k) 1 1 (0+(k+1)+1)
    rw [show 1 + 2 * (1 + k) = 2 * k + 3 from by ring,
        show (0 : ℕ) + (k + 1) + 1 + (1 + k) = 2 * k + 3 from by ring] at h
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by ring]
    rw [show (0 : ℕ) + 1 + (k + 1) = 1 + (1 + k) from by omega]; exact h

-- Phase 2 even
theorem phase2_even (k : ℕ) : ⟨1, 2*k, 0, 0, 2*k⟩ [fm]⊢* ⟨0, 0, 2+2*k, 0, 2*k⟩ := by
  apply stepStar_trans (c₂ := ⟨1+k, 0, 0, 0, 2*k⟩)
  · have h := r3r1r1_chain k 0 0 (2*k)
    rw [show (0 : ℕ) + 1 = 1 from rfl, show (0 : ℕ) + 2 * k = 2 * k from by omega,
        show (0 : ℕ) + 1 + k = 1 + k from by omega] at h
    exact h
  have h := r3_chain (1+k) 0 0 (2*k)
  rw [show (0 : ℕ) + (1 + k) = 1 + k from by omega, show (0 : ℕ) + 2 * (1 + k) = 2 + 2 * k from by ring] at h
  exact h

-- Phase 2 odd
theorem phase2_odd (k : ℕ) : ⟨1, 2*k+1, 0, 0, 2*k+1⟩ [fm]⊢* ⟨0, 0, 2*k+3, 0, 2*k+1⟩ := by
  apply stepStar_trans (c₂ := ⟨1+k, 1, 0, 0, 2*k+1⟩)
  · have h := r3r1r1_chain k 0 1 (2*k+1)
    rw [show (0 : ℕ) + 1 = 1 from rfl, show 1 + 2 * k = 2 * k + 1 from by ring,
        show (0 : ℕ) + 1 + k = 1 + k from by omega] at h
    exact h
  apply stepStar_trans (c₂ := ⟨1+k, 0, 1, 0, 2*k+1⟩)
  · have h := odd_b_step k (2*k+1)
    rw [show k + 1 = 1 + k from by omega] at h; exact h
  have h := r3_chain (1+k) 0 1 (2*k+1)
  rw [show (0 : ℕ) + (1 + k) = 1 + k from by omega, show 1 + 2 * (1 + k) = 2 * k + 3 from by ring] at h
  exact h

-- Phase 3+4: r4_chain then one R5 step
theorem phase34 (n : ℕ) : ⟨0, 0, n+2, 0, n⟩ [fm]⊢⁺ ⟨1, 0, n+1, n+1, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+2, n, 0⟩)
  · have h := r4_chain n (n+2) 0
    rw [show (0 : ℕ) + n = n from by omega] at h; exact h
  apply step_stepPlus
  show fm ⟨0, 0, (n+1)+1, n, 0⟩ = some ⟨0+1, 0, n+1, n+1, 0⟩
  simp [fm]

-- Main transition even
theorem main_trans_even (k : ℕ) : ⟨1, 0, 2*k, 2*k, 0⟩ [fm]⊢⁺ ⟨1, 0, 2*k+1, 2*k+1, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 2*k, 0, 0, 2*k⟩) (phase1_even k)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2+2*k, 0, 2*k⟩) (phase2_even k)
  have h := phase34 (2*k)
  rw [show (2 : ℕ) * k + 2 = 2 + 2 * k from by ring] at h; exact h

-- Main transition odd
theorem main_trans_odd (k : ℕ) : ⟨1, 0, 2*k+1, 2*k+1, 0⟩ [fm]⊢⁺ ⟨1, 0, 2*k+2, 2*k+2, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 2*k+1, 0, 0, 2*k+1⟩) (phase1_odd k)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2*k+3, 0, 2*k+1⟩) (phase2_odd k)
  have h := phase34 (2*k+1)
  rw [show (2 : ℕ) * k + 1 + 2 = 2 * k + 3 from by ring] at h; exact h

-- Combined: (1, 0, n, n, 0) →⁺ (1, 0, n+1, n+1, 0)
theorem main_trans (n : ℕ) : ⟨1, 0, n, n, 0⟩ [fm]⊢⁺ ⟨1, 0, n+1, n+1, 0⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    exact main_trans_even k
  · subst hk
    have h := main_trans_odd k
    rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring]; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨1, 0, n, n, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
