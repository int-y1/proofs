import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #32: [1/15, 28/3, 3/22, 5/2, 11/35, 3/5]

Vector representation:
```
 0 -1 -1  0  0
 2 -1  0  1  0
-1  1  0  0 -1
-1  0  1  0  0
 0  0 -1 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_32

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 chain: (k, 0, c, d, 0) →* (0, 0, c+k, d, 0)
theorem a_to_c : ∀ k, ∀ c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show c + (k + 1) = (c + 1) + k from by ring]
  step fm
  exact h (c + 1) d

-- R4 chain: (0, 0, c+k, k, e) →* (0, 0, c, 0, e+k)
theorem cd_to_e : ∀ k, ∀ c e, ⟨0, 0, c+k, k, e⟩ [fm]⊢* ⟨0, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h c (e + 1))
  ring_nf; finish

-- R2/R1 chain: (a+2, 0, 0, d+1, k) →* (a+k+2, 0, 0, d+k+1, 0)
theorem r2r1_chain : ∀ k, ∀ a d, ⟨a+2, 0, 0, d+1, k⟩ [fm]⊢* ⟨a+k+2, 0, 0, d+k+1, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  rw [show a + 2 = (a + 1) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h (a + 1) (d + 1))
  ring_nf; finish

-- Main transition: (n+1, 0, 0, n, 0) ⊢⁺ (n+2, 0, 0, n+1, 0)
theorem main_trans (n : ℕ) :
    ⟨n+1, 0, 0, n, 0⟩ [fm]⊢⁺ ⟨n+2, 0, 0, n+1, 0⟩ := by
  -- Phase 1: first R3 step (gives us ⊢⁺)
  apply step_stepStar_stepPlus
  · show fm ⟨n + 1, 0, 0, n, 0⟩ = some ⟨n, 0, 1, n, 0⟩; simp [fm]
  -- Remaining R3 steps: (n, 0, 1, n, 0) →* (0, 0, n+1, n, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, 1 + n, n, 0⟩)
  · exact a_to_c n 1 n
  -- R4 chain: (0, 0, 1+n, n, 0) →* (0, 0, 1, 0, n)
  apply stepStar_trans (c₂ := ⟨0, 0, 1, 0, n⟩)
  · have h := cd_to_e n 1 0
    simp only [Nat.zero_add] at h; exact h
  -- R5 + R1: (0, 0, 1, 0, n) →* (2, 0, 0, 1, n)
  apply stepStar_trans (c₂ := ⟨2, 0, 0, 1, n⟩)
  · step fm; step fm; finish
  -- R2/R1 chain: (2, 0, 0, 1, n) →* (n+2, 0, 0, n+1, 0)
  have h := r2r1_chain n 0 0
  simp only [Nat.zero_add] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, n+1, 0⟩) 0
  intro n; exact ⟨n+1, main_trans (n+1)⟩

end Sz22_2003_unofficial_32
