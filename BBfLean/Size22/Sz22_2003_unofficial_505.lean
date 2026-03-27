import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #505: [28/15, 3/22, 35/2, 11/49, 6/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  1  1  0
 0  0  0 -2  1
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_505

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: drain d by 2, build e
theorem r4_drain : ⟨(0 : ℕ), 0, c, d + 2*k, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, k⟩ := by
  have h : ∀ k e, ⟨(0 : ℕ), 0, c, d + 2*k, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, e + k⟩ := by
    intro k; induction' k with k ih <;> intro e
    · simp; exists 0
    rw [show d + 2 * (k + 1) = d + 2 * k + 2 from by ring]
    step fm; apply stepStar_trans (ih _); ring_nf; finish
  have := h k 0; simp at this; exact this

-- R2+R1 chain
theorem r2r1_chain : ⟨A + 1, 0, k, D, E + k⟩ [fm]⊢* ⟨A + 1 + k, 0, 0, D + k, E⟩ := by
  have h : ∀ k A D, ⟨A + 1, 0, k, D, E + k⟩ [fm]⊢* ⟨A + 1 + k, 0, 0, D + k, E⟩ := by
    intro k; induction' k with k ih <;> intro A D
    · exists 0
    rw [show E + (k + 1) = E + k + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (A + 1) (D + 1)); ring_nf; finish
  exact h k A D

-- R2 drain
theorem r2_drain : ⟨A + k, B, 0, D, k⟩ [fm]⊢* ⟨A, B + k, 0, D, (0 : ℕ)⟩ := by
  have h : ∀ k B, ⟨A + k, B, 0, D, k⟩ [fm]⊢* ⟨A, B + k, 0, D, (0 : ℕ)⟩ := by
    intro k; induction' k with k ih <;> intro B
    · simp; exists 0
    rw [show A + (k + 1) = A + k + 1 from by ring]
    step fm; apply stepStar_trans (ih (B + 1)); ring_nf; finish
  exact h k B

-- R3+R1 chain
theorem r3r1_chain : ⟨A + 1, k, 0, D, (0 : ℕ)⟩ [fm]⊢* ⟨A + 1 + k, 0, 0, D + 2*k, (0 : ℕ)⟩ := by
  have h : ∀ k A D, ⟨A + 1, k, 0, D, (0 : ℕ)⟩ [fm]⊢* ⟨A + 1 + k, 0, 0, D + 2*k, (0 : ℕ)⟩ := by
    intro k; induction' k with k ih <;> intro A D
    · exists 0
    step fm; step fm
    apply stepStar_trans (ih (A + 1) (D + 2)); ring_nf; finish
  exact h k A D

-- R3 drain
theorem r3_drain : ⟨k, 0, C, D, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), 0, C + k, D + k, (0 : ℕ)⟩ := by
  have h : ∀ k C D, ⟨k, 0, C, D, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), 0, C + k, D + k, (0 : ℕ)⟩ := by
    intro k; induction' k with k ih <;> intro C D
    · exists 0
    step fm; apply stepStar_trans (ih (C + 1) (D + 1)); ring_nf; finish
  exact h k C D

-- Full transition: (0, 0, n+2, 4n+5, 0) ⊢⁺ (0, 0, n+3, 4n+9, 0)
theorem full_trans (n : ℕ) : ⟨(0 : ℕ), 0, n+2, 4*n+5, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, n+3, 4*n+9, 0⟩ := by
  -- R4 drain: (0,0,n+2,4n+5,0) →* (0,0,n+2,1,2n+2)
  rw [show 4*n+5 = 1 + 2*(2*n+2) from by ring]
  apply stepStar_stepPlus_stepPlus (@r4_drain (n+2) 1 (2*n+2))
  -- R5 + R1: (0,0,n+2,1,2n+2) → (1,1,n+1,1,2n+2) → (3,0,n,2,2n+2)
  step fm; step fm
  -- R2+R1 chain: (3,0,n,2,2n+2) →* (n+3,0,0,n+2,n+2)
  rw [show (2 * n + 2 : ℕ) = (n + 2) + n from by ring]
  apply stepStar_trans (@r2r1_chain 2 n 2 (n+2))
  -- R2 drain: (n+3,0,0,n+2,n+2) →* (1,n+2,0,n+2,0)
  rw [show 2 + 1 + n = 1 + (n + 2) from by ring,
      show 2 + n = n + 2 from by ring]
  apply stepStar_trans (@r2_drain 1 (n+2) 0 (n+2))
  -- R3+R1 chain: (1,n+2,0,n+2,0) →* (n+3,0,0,3n+6,0)
  rw [show (0 + (n + 2) : ℕ) = n + 2 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (@r3r1_chain 0 (n+2) (n+2))
  -- R3 drain: (n+3,0,0,3n+6,0) →* (0,0,n+3,4n+9,0)
  rw [show 0 + 1 + (n + 2) = n + 3 from by ring,
      show n + 2 + 2 * (n + 2) = 3 * n + 6 from by ring]
  apply stepStar_trans (@r3_drain (n+3) 0 (3*n+6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 5, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n+2, 4*n+5, 0⟩) 0
  intro n; exact ⟨n+1, full_trans n⟩
