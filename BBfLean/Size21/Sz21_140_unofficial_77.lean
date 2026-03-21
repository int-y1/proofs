import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #77: [5/6, 196/55, 121/2, 3/7, 5/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1  2 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_77

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 repeated: a → e
theorem a_to_e : ∀ k, ∀ a e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R4 repeated: d → b
theorem d_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R2 repeated: c,e → a,d
theorem r2_chain : ∀ k, ∀ a c d, ⟨a, 0, c+k, d, k⟩ [fm]⊢* ⟨a+2*k, 0, c, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R1R1R2 rounds
theorem r1r1r2_rounds : ∀ j, ∀ c d, ⟨2, 2*j, c, d, 2*j+c⟩ [fm]⊢* ⟨2, 0, c+j, d+2*j, c+j⟩ := by
  intro j; induction' j with j ih <;> intro c d
  · ring_nf; exists 0
  rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring,
      show (2 * j + 1 + 1 : ℕ) + c = (2 * j + 1) + (c + 1) from by ring]
  step fm
  rw [show (2 * j + 1 : ℕ) = 2 * j + 1 from rfl]
  step fm
  rw [show (c + 1 + 1 : ℕ) = (c + 1) + 1 from by ring,
      show (2 * j + 1 + (c + 1) : ℕ) = (2 * j + (c + 1)) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (c + 1) (d + 2))
  ring_nf; finish

-- Main transition
theorem main_trans (N : ℕ) : ⟨N+1, 0, 0, 2*N, 0⟩ [fm]⊢⁺ ⟨2*N+2, 0, 0, 4*N+2, 0⟩ := by
  -- Phase 1: R3 × (N+1): a → e
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 2*N, 2*(N+1)⟩)
  · have h := a_to_e (N+1) 0 0 (d := 2*N)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 × (2*N): d → b
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*N, 0, 0, 2*(N+1)⟩)
  · have h := d_to_b (2*N) 0 0 (e := 2*(N+1))
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*N, 1, 0, 2*N+1⟩)
  · show fm ⟨0, 2*N, 0, 0, (2*N+1)+1⟩ = some ⟨0, 2*N, 1, 0, 2*N+1⟩
    simp [fm]
  -- Phase 4: R2
  apply stepStar_trans (c₂ := ⟨2, 2*N, 0, 2, 2*N⟩)
  · rw [show (1 : ℕ) = 0 + 1 from rfl, show (2*N+1 : ℕ) = (2*N) + 1 from by ring]
    exact step_stepStar (show fm ⟨0, 2*N, 0+1, 0, (2*N)+1⟩ = some ⟨2, 2*N, 0, 2, 2*N⟩ from by simp [fm])
  -- Phase 5: R1R1R2 rounds × N
  apply stepStar_trans (c₂ := ⟨2, 0, N, 2+2*N, N⟩)
  · have h := r1r1r2_rounds N 0 2
    rw [show 2 * N + 0 = 2 * N from by ring, show 0 + N = N from by ring] at h; exact h
  -- Phase 6: R2 × N
  have h := r2_chain N 2 0 (2+2*N)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun N ↦ ⟨N+1, 0, 0, 2*N, 0⟩) 0
  intro N
  refine ⟨2*N+1, ?_⟩
  have h := main_trans N
  convert h using 2; ring_nf
