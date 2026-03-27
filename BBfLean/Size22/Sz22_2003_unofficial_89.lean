import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #89: [1/30, 15/77, 49/3, 4/7, 363/2]

Vector representation:
```
-1 -1 -1  0  0
 0  1  1 -1 -1
 0 -1  0  2  0
 2  0  0 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_89

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R3 drain: (0, b+k, c, d, 0) ->* (0, b, c, d+2*k, 0)
theorem r3_drain : ∀ k b c d, ⟨0, b+k, c, d, 0⟩ [fm]⊢* ⟨0, b, c, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro b c d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 chain: (a, 0, c, d+k, 0) ->* (a+2*k, 0, c, d, 0)
theorem r4_chain : ∀ k a c d, ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a+2*k, 0, c, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5/R1 chain: (a+2*k, 0, c+k, 0, e) ->* (a, 0, c, 0, e+2*k)
theorem r5r1_chain : ∀ k a c e, ⟨a+2*k, 0, c+k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring,
      show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3/R2/R2 chain: (0, b+1, c, 0, e+2*k) ->* (0, b+1+k, c+2*k, 0, e)
theorem r3r2r2_chain : ∀ k b c e, ⟨0, b+1, c, 0, e+2*k⟩ [fm]⊢* ⟨0, b+1+k, c+2*k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro b c e
  · exists 0
  rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
  step fm
  rw [show (e + 2 * k) + 2 = (e + 2 * k + 1) + 1 from by ring]
  step fm
  rw [show e + 2 * k + 1 = (e + 2 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Tail: (4, 0, 0, 0, e) ->* (1, 0, 0, 0, e)
theorem tail (e : ℕ) : ⟨4, 0, 0, 0, e⟩ [fm]⊢* ⟨1, 0, 0, 0, e⟩ := by
  step fm
  step fm
  rw [show e + 2 = (e + 1) + 1 from by ring]
  step fm
  step fm
  step fm
  step fm
  finish

-- Main transition: (1, 0, 0, 0, 2*n) ⊢⁺ (1, 0, 0, 0, 4*n+4)
theorem main_trans (n : ℕ) : ⟨1, 0, 0, 0, 2*n⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 4*n+4⟩ := by
  -- R5: (1,0,0,0,2*n) -> (0,1,0,0,2*n+2)
  step fm
  -- R3: (0,1,0,0,2*n+2) -> (0,0,0,2,2*n+2)
  step fm
  -- R2: (0,0,0,2,2*n+2) -> (0,1,1,1,2*n+1)
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  -- R2: (0,1,1,1,2*n+1) -> (0,2,2,0,2*n)
  rw [show 2 * n + 1 = (2 * n) + 1 from by ring]
  step fm
  -- Phase B2: n rounds of R3/R2/R2: (0,2,2,0,2*n) -> (0,n+2,2*n+2,0,0)
  apply stepStar_trans (c₂ := ⟨0, n+2, 2*n+2, 0, 0⟩)
  · have h := r3r2r2_chain n 1 2 0
    simp only [Nat.zero_add, (by ring : 1 + 1 + n = n + 2),
               (by ring : 1 + 1 = 2), (by ring : 2 + 2 * n = 2 * n + 2)] at h; exact h
  -- Phase C: R3 drain: (0,n+2,2*n+2,0,0) -> (0,0,2*n+2,2*n+4,0)
  apply stepStar_trans (c₂ := ⟨0, 0, 2*n+2, 2*n+4, 0⟩)
  · have h := r3_drain (n+2) 0 (2*n+2) 0
    simp only [Nat.zero_add, (by ring : 2 * (n + 2) = 2 * n + 4)] at h; exact h
  -- Phase D: R4 chain: (0,0,2*n+2,2*n+4,0) -> (4*n+8,0,2*n+2,0,0)
  apply stepStar_trans (c₂ := ⟨4*n+8, 0, 2*n+2, 0, 0⟩)
  · have h := r4_chain (2*n+4) 0 (2*n+2) 0
    simp only [Nat.zero_add, (by ring : 2 * (2 * n + 4) = 4 * n + 8)] at h; exact h
  -- Phase E: R5/R1 chain: (4*n+8,0,2*n+2,0,0) -> (4,0,0,0,4*n+4)
  apply stepStar_trans (c₂ := ⟨4, 0, 0, 0, 4*n+4⟩)
  · have h := r5r1_chain (2*n+2) 4 0 0
    simp only [(by ring : 4 + 2 * (2 * n + 2) = 4 * n + 8),
               (by ring : 0 + (2 * n + 2) = 2 * n + 2),
               (by ring : 0 + 2 * (2 * n + 2) = 4 * n + 4)] at h; exact h
  -- Phase F: Tail: (4,0,0,0,4*n+4) -> (1,0,0,0,4*n+4)
  exact tail (4*n+4)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨1, 0, 0, 0, 2*n⟩) 0
  intro n; exists 2*n+2
  show ⟨1, 0, 0, 0, 2*n⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2*(2*n+2)⟩
  rw [show 2*(2*n+2) = 4*n+4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_89
