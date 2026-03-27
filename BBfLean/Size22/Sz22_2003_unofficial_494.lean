import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #494: [28/15, 3/22, 25/2, 11/7, 98/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  1
 1  0 -1  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_494

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

-- R4 repeated: drain d to e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 repeated: drain a to c (b=0, e=0)
theorem a_to_c : ∀ k a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2/R1 chain: each pair does R2 then R1
theorem r2r1_chain : ∀ k a c d e, ⟨a + 1, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + k, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R2
  step fm  -- R1
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Main transition: (0, 0, (k+1)^2+2, 2(k+1), 0) ⊢⁺ (0, 0, (k+2)^2+2, 2(k+2), 0)
theorem main_trans (k : ℕ) :
    ⟨0, 0, (k + 1) * (k + 1) + 2, 2 * (k + 1), 0⟩ [fm]⊢⁺
    ⟨0, 0, (k + 2) * (k + 2) + 2, 2 * (k + 2), 0⟩ := by
  -- Phase 1: d_to_e
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_e (2 * (k + 1)) ((k + 1) * (k + 1) + 2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step (gives ⊢⁺ via step fm)
  step fm
  -- Now at: (1, 0, (k+1)^2+1, 2, 2*(k+1))
  -- Phase 3: r2r1_chain with 2*(k+1) rounds
  -- (k+1)^2+1 = k*k + 2*k + 2 = k*k + 2*(k+1)
  rw [show (k + 1) * (k + 1) + 1 = k * k + 2 * (k + 1) from by ring]
  apply stepStar_trans (c₂ := ⟨2 * (k + 1) + 1, 0, k * k, 2 + 2 * (k + 1), 0⟩)
  · have h := r2r1_chain (2 * (k + 1)) 0 (k * k) 2 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 4: a_to_c
  rw [show (k + 2) * (k + 2) + 2 = k * k + 2 * (2 * (k + 1) + 1) from by ring,
      show 2 * (k + 2) = 2 + 2 * (k + 1) from by ring]
  have h := a_to_c (2 * (k + 1) + 1) 0 (k * k) (2 + 2 * (k + 1))
  simp only [Nat.zero_add] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 6, 4, 0⟩) (by execute fm 13)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, (k + 1) * (k + 1) + 2, 2 * (k + 1), 0⟩) 1
  intro k; exists k + 1; exact main_trans k

end Sz22_2003_unofficial_494
