import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #455: [28/15, 1/6, 9/7, 625/2, 3/5]

Vector representation:
```
 2 -1 -1  1
-1 -1  0  0
 0  2  0 -1
-1  0  4  0
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_455

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+1⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+4, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- Phase 1: R4 repeated, converts a to c
theorem a_to_c : ∀ k a c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+4*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Phase 2b: R3,R1,R1 chain consuming c in pairs
theorem r3r1r1_chain : ∀ k a d, ⟨a, 0, 2*k, d+1⟩ [fm]⊢* ⟨a+4*k, 0, 0, d+k+1⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  rw [show 2 * (k + 1) = (2 * k) + 2 from by ring]
  step fm  -- R3: (a, 2, 2k+2, d)
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm  -- R1: (a+2, 1, 2k+1, d+1)
  rw [show 2 * k + 1 = 2 * k + 1 from by ring]
  step fm  -- R1: (a+4, 0, 2k, d+2)
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Phase 3: R3,R2,R2 drain
theorem drain : ∀ k a, ⟨a+2*k, 0, 0, k⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a
  · exists 0
  rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring]
  step fm  -- R3: (a+2k+2, 2, 0, k)
  step fm  -- R2: (a+2k+1, 1, 0, k)
  step fm  -- R2: (a+2k, 0, 0, k)
  exact h _

-- Main transition: (n+2, 0, 0, 0) ⊢⁺ (4*n+6, 0, 0, 0)
theorem main_trans (n : ℕ) : ⟨n+2, 0, 0, 0⟩ [fm]⊢⁺ ⟨4*n+6, 0, 0, 0⟩ := by
  -- Phase 1: (n+2, 0, 0, 0) ⊢* (0, 0, 4*(n+2), 0)
  apply stepStar_stepPlus_stepPlus
  · have h := a_to_c (n+2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Now at (0, 0, 4n+8, 0)
  -- Phase 2a: R5, R1
  rw [show 4 * (n + 2) = (2 * (2 * n + 3) + 1) + 1 from by ring]
  step fm  -- R5: (0, 1, 2*(2n+3)+1, 0)
  rw [show 2 * (2 * n + 3) + 1 = 2 * (2 * n + 3) + 1 from by ring]
  step fm  -- R1: (2, 0, 2*(2n+3), 1)
  -- Phase 2b: R3,R1,R1 chain with k=2n+3, d=0
  apply stepStar_trans
  · have h := r3r1r1_chain (2*n+3) 2 0
    simp only [Nat.zero_add] at h; exact h
  -- Now at (2+4*(2n+3), 0, 0, 0+(2n+3)+1) = (8n+14, 0, 0, 2n+4)
  -- Phase 3: drain with k=2n+4, a=4n+6
  have h := drain (2*n+4) (4*n+6)
  simp only [(by ring : 4 * n + 6 + 2 * (2 * n + 4) = 2 + 4 * (2 * n + 3))] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+2, 0, 0, 0⟩) 0
  intro n; exists 4*n+4
  exact main_trans n

end Sz22_2003_unofficial_455
