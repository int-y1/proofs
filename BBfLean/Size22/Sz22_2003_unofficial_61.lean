import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #61: [1/15, 98/3, 9/539, 5/7, 99/2]

Vector representation:
```
 0 -1 -1  0  0
 1 -1  0  2  0
 0  2  0 -2 -1
 0  0  1 -1  0
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_61

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- R2R2R3 chain: k rounds of (R2, R2, R3)
-- Each round from (A, 2, 0, D, E) does:
--   R2: (A+1, 1, 0, D+2, E) -> R2: (A+2, 0, 0, D+4, E) -> R3: (A+2, 2, 0, D+2, E-1)
-- Net: A+=2, D+=2, E-=1
theorem r2r2r3_chain : ∀ k, ∀ A D, ⟨A, 2, 0, D, k⟩ [fm]⊢* ⟨A+2*k, 2, 0, D+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro A D
  · exists 0
  -- state: (A, 1+1, 0, D, k+1)
  -- R2 fires (b=1+1>=1, c=0): → (A+1, 1, 0, D+2, k+1)
  step fm
  -- R2 fires (b=1>=1, c=0): → (A+2, 0, 0, D+4, k+1)
  step fm
  -- R3 fires (d=D+4>=2, e=k+1>=1): → (A+2, 2, 0, D+2, k)
  rw [show D + 2 + 2 = (D + 2) + 2 from by ring,
      show k + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (h (A + 2) (D + 2))
  ring_nf; finish

-- R2R2 final: (A, 2, 0, D, 0) →* (A+2, 0, 0, D+4, 0)
theorem r2r2_final : ∀ A D, ⟨A, 2, 0, D, 0⟩ [fm]⊢* ⟨A+2, 0, 0, D+4, 0⟩ := by
  intro A D
  -- R2: (A, 1+1, 0, D, 0) → (A+1, 1, 0, D+2, 0)
  step fm
  -- R2: (A+1, 1, 0, D+2, 0) → (A+2, 0, 0, D+4, 0)
  step fm
  rw [show D + 2 + 2 = D + 4 from by ring]
  finish

-- R4 chain: (A, 0, c, k, 0) →* (A, 0, c+k, 0, 0)
theorem d_to_c : ∀ k, ∀ A c, ⟨A, 0, c, k, 0⟩ [fm]⊢* ⟨A, 0, c+k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro A c
  · exists 0
  rw [show k + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (h A (c + 1))
  ring_nf; finish

-- R5R1R1 chain: k rounds of (R5, R1, R1)
-- (a+k, 0, 2*k, 0, E) →* (a, 0, 0, 0, E+k)
theorem r5r1r1_chain : ∀ k, ∀ a E, ⟨a+k, 0, 2*k, 0, E⟩ [fm]⊢* ⟨a, 0, 0, 0, E+k⟩ := by
  intro k; induction' k with k h <;> intro a E
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  -- R5: (a+k+1, 0, 2k+2, 0, E) → (a+k, 2, 2k+2, 0, E+1)
  step fm
  -- R1: (a+k, 2, 2k+2, 0, E+1) → (a+k, 1, 2k+1, 0, E+1)
  step fm
  -- R1: (a+k, 1, 2k+1, 0, E+1) → (a+k, 0, 2k, 0, E+1)
  step fm
  apply stepStar_trans (h a (E + 1))
  ring_nf; finish

-- Main transition: (a+1, 0, 0, 0, e+1) →⁺ (a+e+2, 0, 0, 0, e+4)
theorem main_trans (a e : ℕ) : ⟨a+1, 0, 0, 0, e+1⟩ [fm]⊢⁺ ⟨a+e+2, 0, 0, 0, e+4⟩ := by
  -- R5: → (a, 2, 0, 0, e+2)
  apply step_stepStar_stepPlus (c₂ := ⟨a, 2, 0, 0, e+2⟩)
  · show fm ⟨a + 1, 0, 0, 0, e + 1⟩ = some ⟨a, 2, 0, 0, e + 2⟩; simp [fm]
  -- R2R2R3 chain with k=e+2
  apply stepStar_trans (c₂ := ⟨a + 2 * (e + 2), 2, 0, 2 * (e + 2), 0⟩)
  · have h := r2r2r3_chain (e + 2) a 0; simp only [Nat.zero_add] at h; exact h
  -- R2R2 final
  apply stepStar_trans (c₂ := ⟨a + 2 * (e + 2) + 2, 0, 0, 2 * (e + 2) + 4, 0⟩)
  · exact r2r2_final (a + 2 * (e + 2)) (2 * (e + 2))
  -- R4 chain
  apply stepStar_trans (c₂ := ⟨a + 2 * (e + 2) + 2, 0, 2 * (e + 2) + 4, 0, 0⟩)
  · have h := d_to_c (2 * (e + 2) + 4) (a + 2 * (e + 2) + 2) 0
    simp only [Nat.zero_add] at h; exact h
  -- R5R1R1 chain with k=e+4
  have h := r5r1r1_chain (e + 4) (a + e + 2) 0
  simp only [Nat.zero_add] at h
  rw [show a + 2 * (e + 2) + 2 = a + e + 2 + (e + 4) from by ring,
      show 2 * (e + 2) + 4 = 2 * (e + 4) from by ring]
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 3⟩) (by execute fm 21)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a+1, 0, 0, 0, e+3⟩) ⟨0, 0⟩
  intro ⟨a, e⟩
  exact ⟨⟨a + e + 3, e + 3⟩, by convert main_trans a (e + 2) using 2⟩

end Sz22_2003_unofficial_61
