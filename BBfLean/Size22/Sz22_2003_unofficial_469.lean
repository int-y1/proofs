import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #469: [28/15, 21/22, 25/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  1 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_469

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: convert d to e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 repeated: convert a to c (each step adds 2 to c)
theorem a_to_c : ∀ k a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Interleaved R1/R2 chain with final R1:
-- (a, 1, c+j+1, d, j) ⊢* (a+j+2, 0, c, d+2*j+1, 0)
theorem interleaved : ∀ j, ∀ a c d,
    ⟨a, 1, c + j + 1, d, j⟩ [fm]⊢* ⟨a + j + 2, 0, c, d + 2 * j + 1, 0⟩ := by
  intro j; induction' j with j h <;> intro a c d
  · -- j=0: just R1
    step fm
    ring_nf; finish
  · -- j+1: R1, R2, then IH
    rw [show c + (j + 1) + 1 = (c + j + 1) + 1 from by ring]
    step fm  -- R1: (a+2, 0, c+j+1, d+1, j+1)
    rw [show (j : ℕ) + 1 = j + 1 from rfl]
    step fm  -- R2: (a+1, 1, c+j+1, d+2, j)
    apply stepStar_trans (h (a + 1) c (d + 2))
    ring_nf; finish

-- Main transition: (0, 0, c+e+3, 0, e+1) ⊢⁺ (0, 0, c+2*e+6, 0, 2*e+3)
theorem main_trans (c e : ℕ) :
    ⟨0, 0, c + e + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * e + 6, 0, 2 * e + 3⟩ := by
  -- Phase 1: R5
  rw [show c + e + 3 = (c + e + 2) + 1 from by ring,
      show (e : ℕ) + 1 = e + 1 from rfl]
  step fm  -- R5: (0, 1, c+e+2, 0, e+1)
  -- Phase 2: interleaved chain
  rw [show c + e + 2 = c + (e + 1) + 1 from by ring]
  apply stepStar_trans (interleaved (e + 1) 0 c 0)
  -- Now at (0+(e+1)+2, 0, c, 0+2*(e+1)+1, 0); normalize
  rw [show 0 + (e + 1) + 2 = 0 + (e + 3) from by ring,
      show 0 + 2 * (e + 1) + 1 = 2 * e + 3 from by ring]
  -- Phase 3: a_to_c
  apply stepStar_trans (a_to_c (e + 3) 0 c (2 * e + 3))
  -- Phase 4: d_to_e
  rw [show c + 2 * (e + 3) = c + 2 * e + 6 from by ring]
  have h := d_to_e (2 * e + 3) (c + 2 * e + 6) 0 0
  simp only [Nat.zero_add] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 1⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, e⟩ ↦ ⟨0, 0, c + e + 3, 0, e + 1⟩) ⟨1, 0⟩
  intro ⟨c, e⟩
  exact ⟨⟨c + 1, 2 * e + 2⟩, by
    show ⟨0, 0, c + e + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, (c + 1) + (2 * e + 2) + 3, 0, (2 * e + 2) + 1⟩
    rw [show (c + 1) + (2 * e + 2) + 3 = c + 2 * e + 6 from by ring,
        show (2 * e + 2) + 1 = 2 * e + 3 from by ring]
    exact main_trans c e⟩

end Sz22_2003_unofficial_469
