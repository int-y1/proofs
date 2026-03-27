import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #487: [28/15, 3/22, 25/2, 1/3, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0 -1  0  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_487

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 repeated: drain a to c (b=0, e=0)
theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R5 repeated: drain d to e (a=0, b=0)
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R1,R2 chain: k pairs
-- (i, 1, c+k, d, k) ⊢* (i+k, 1, c, d+k, 0)
theorem r1r2_chain : ∀ k, ∀ i c d, ⟨i, 1, c+k, d, k⟩ [fm]⊢* ⟨i+k, 1, c, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro i c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm  -- R1: (i+2, 0, c+k, d+1, k+1)
  step fm  -- R2: (i+1, 1, c+k, d+1, k)
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- Main transition: (n+1, 0, c, n, 0) ⊢⁺ (n+2, 0, c+n, n+1, 0)
theorem main_trans (n c : ℕ) : ⟨n+1, 0, c, n, 0⟩ [fm]⊢⁺ ⟨n+2, 0, c+n, n+1, 0⟩ := by
  -- First R3 step: (n+1, 0, c, n, 0) ⊢ (n, 0, c+2, n, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨n + 1, 0, c, n, 0⟩ = some ⟨n, 0, c + 2, n, 0⟩; simp [fm]
  -- Remaining R3 steps: (n, 0, c+2, n, 0) ⊢* (0, 0, c+2+2*n, n, 0)
  apply stepStar_trans
  · have h := a_to_c n 0 (c+2) n; simp only [Nat.zero_add] at h; exact h
  -- d_to_e: (0, 0, c+2+2*n, n, 0) ⊢* (0, 0, c+2+2*n, 0, n)
  apply stepStar_trans
  · have h := d_to_e n (c+2+2*n) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R6: (0, 0, c+2+2*n, 0, n) -> (0, 1, c+2*n+1, 0, n)
  rw [show c + 2 + 2 * n = (c + 2 * n + 1) + 1 from by ring]
  step fm  -- R6: (0, 1, c+2*n+1, 0, n)
  -- r1r2_chain: rewrite c+2*n+1 = (c+n+1)+n
  apply stepStar_trans
  · rw [show c + 2 * n + 1 = (c + n + 1) + n from by ring]
    exact r1r2_chain n 0 (c+n+1) 0
  -- After chain: (0+n, 1, c+n+1, 0+n, 0). Simplify Nat.zero+n.
  simp only [Nat.zero_add]
  -- Final R1: (n, 1, c+n+1, n, 0) -> (n+2, 0, c+n, n+1, 0)
  rw [show c + n + 1 = (c + n) + 1 from by ring]
  step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, c⟩ ↦ ⟨n+1, 0, c, n, 0⟩) ⟨0, 0⟩
  intro ⟨n, c⟩; exact ⟨⟨n+1, c+n⟩, main_trans n c⟩

end Sz22_2003_unofficial_487
