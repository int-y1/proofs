import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #51: [1/15, 9/154, 4/3, 35/2, 363/5]

Vector representation:
```
 0 -1 -1  0  0
-1  2  0 -1 -1
 2 -1  0  0  0
-1  0  1  1  0
 0  1 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_51

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- Phase 1: R3 chain: (a+k, 0, c, d, 0) ⊢* (a, 0, c+k, d+k, 0)
theorem a_to_cd : ∀ k, ∀ a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · simp; exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h a (c + 1) (d + 1))
  ring_nf; finish

-- Phase 2: R4,R0 chain for odd c: (0, 0, 2*k+1, d, e) ⊢* (0, 1, 0, d, e+2*k+2)
theorem r4r0_chain : ∀ k, ∀ d e, ⟨0, 0, 2*k+1, d, e⟩ [fm]⊢* ⟨0, 1, 0, d, e+2*k+2⟩ := by
  intro k; induction' k with k h <;> intro d e
  · step fm; finish
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (h d (e + 2))
  ring_nf; finish

-- Phase 3: R1,R1,R2 chain: (2, b, 0, d+2*k, e+2*k) ⊢* (2, b+3*k, 0, d, e)
theorem r1r1r2_chain : ∀ k, ∀ b d e, ⟨2, b, 0, d+2*k, e+2*k⟩ [fm]⊢* ⟨2, b+3*k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · simp; exists 0
  rw [show d + 2 * (k + 1) = d + 2 * k + 2 from by ring,
      show e + 2 * (k + 1) = e + 2 * k + 2 from by ring]
  -- State: (2, b, 0, d+2k+2, e+2k+2) = (1+1, b, 0, (d+2k+1)+1, (e+2k+1)+1)
  -- R1: -> (1, b+2, 0, d+2k+1, e+2k+1) = (0+1, b+2, 0, (d+2k)+1, (e+2k)+1)
  -- R1: -> (0, b+4, 0, d+2k, e+2k)
  -- R2: -> (2, b+3, 0, d+2k, e+2k)
  have h1 : fm ⟨2, b, 0, d + 2 * k + 2, e + 2 * k + 2⟩ = some ⟨1, b + 2, 0, d + 2 * k + 1, e + 2 * k + 1⟩ := by
    simp [fm]
  have h2 : fm ⟨1, b + 2, 0, d + 2 * k + 1, e + 2 * k + 1⟩ = some ⟨0, b + 4, 0, d + 2 * k, e + 2 * k⟩ := by
    simp [fm]
  have h3 : fm ⟨0, b + 4, 0, d + 2 * k, e + 2 * k⟩ = some ⟨2, b + 3, 0, d + 2 * k, e + 2 * k⟩ := by
    simp [fm]
  apply stepStar_trans (step_stepStar h1)
  apply stepStar_trans (step_stepStar h2)
  apply stepStar_trans (step_stepStar h3)
  apply stepStar_trans (h (b + 3) d e)
  ring_nf; finish

-- Phase 4: R2 chain: (a, b+k, 0, 0, e) ⊢* (a+2*k, b, 0, 0, e)
theorem b_to_a : ∀ k, ∀ a b e, ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+2*k, b, 0, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a b e
  · simp; exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h (a + 2) b e)
  ring_nf; finish

-- Main transition: (2*n+5, 0, 0, 0, 0) ⊢⁺ (6*n+17, 0, 0, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨2*n+5, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨6*n+17, 0, 0, 0, 0⟩ := by
  -- Phase 1: R3 chain: (2n+5, 0, 0, 0, 0) -> (0, 0, 2n+5, 2n+5, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2*n+5, 2*n+5, 0⟩)
  · have h := a_to_cd (2*n+5) 0 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4,R0 chain: (0, 0, 2n+5, 2n+5, 0) -> (0, 1, 0, 2n+5, 2n+6)
  -- c = 2*(n+2)+1, so k = n+2
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 0, 2*n+5, 2*n+6⟩)
  · have h := r4r0_chain (n+2) (2*n+5) 0
    rw [show 2 * (n + 2) + 1 = 2 * n + 5 from by ring,
        show 0 + 2 * (n + 2) + 2 = 2 * n + 6 from by ring] at h
    exact h
  -- R2: (0, 1, 0, 2n+5, 2n+6) -> (2, 0, 0, 2n+5, 2n+6)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 0, 0, 2*n+5, 2*n+6⟩)
  · step fm; finish
  -- Phase 3: R1,R1,R2 chain with k=n+2 rounds
  -- (2, 0, 0, 2n+5, 2n+6) = (2, 0, 0, 1+2*(n+2), 2+2*(n+2))
  -- -> (2, 3*(n+2), 0, 1, 2) = (2, 3n+6, 0, 1, 2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 3*n+6, 0, 1, 2⟩)
  · have h := r1r1r2_chain (n+2) 0 1 2
    rw [show 1 + 2 * (n + 2) = 2 * n + 5 from by ring,
        show 2 + 2 * (n + 2) = 2 * n + 6 from by ring,
        show 0 + 3 * (n + 2) = 3 * n + 6 from by ring] at h
    exact h
  -- R1: (2, 3n+6, 0, 1, 2) -> (1, 3n+8, 0, 0, 1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 3*n+8, 0, 0, 1⟩)
  · step fm; finish
  -- Phase 4: R2 chain: (1, 3n+8, 0, 0, 1) -> (6n+17, 0, 0, 0, 1)
  -- b = 0 + (3n+8), so k = 3n+8
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨6*n+17, 0, 0, 0, 1⟩)
  · have h := b_to_a (3*n+8) 1 0 1
    rw [show 1 + 2 * (3 * n + 8) = 6 * n + 17 from by ring,
        show 0 + (3 * n + 8) = 3 * n + 8 from by ring] at h
    exact h
  -- Cleanup: (6n+17, 0, 0, 0, 1) -> (6n+17, 0, 0, 0, 0)
  -- R3: (6n+16, 0, 1, 1, 1) -> R1: (6n+15, 2, 1, 0, 0) -> R0: (6n+15, 1, 0, 0, 0) -> R2: (6n+17, 0, 0, 0, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨6*n+17, 0, 0, 0, 1⟩ = some ⟨6*n+16, 0, 1, 1, 1⟩
    simp [fm]
  rw [show 6*n+16 = (6*n+15) + 1 from by ring]
  step fm; step fm; step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2*n+5, 0, 0, 0, 0⟩) 0
  intro n; exact ⟨3*n+6, by
    show ⟨2*n+5, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨2*(3*n+6)+5, 0, 0, 0, 0⟩
    rw [show 2*(3*n+6)+5 = 6*n+17 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_51
