import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #507: [28/15, 3/22, 5/2, 11/7, 126/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  1  0  0
 0  0  0 -1  1
 1  2 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_507

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+2, c, d+1, e⟩
  | _ => none

-- R3 repeated: transfer a to c (b=0, e=0)
theorem a_to_c : ∀ k a c, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R4 repeated: transfer d to e (a=0, b=0)
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5+R1+R1 (3 steps)
theorem r5r1r1 : ⟨0, 0, c+3, 0, e⟩ [fm]⊢* ⟨5, 0, c, 3, e⟩ := by
  step fm; step fm; step fm; finish

-- R2+R1 interleaved chain: each round does R2 then R1
theorem r2r1_chain : ∀ k a c d e, ⟨a+1, 0, c+k, d, e+k⟩ [fm]⊢* ⟨a+1+k, 0, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h (a+1) c (d+1) e)
  ring_nf; finish

-- R2 repeated: transfer e to b (c=0)
theorem e_to_b : ∀ k a b d, ⟨a+k, b, 0, d, k⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h a (b+1) d)
  ring_nf; finish

-- R3+R1 interleaved chain: each round does R3 then R1
theorem r3r1_chain : ∀ k a b d, ⟨a+1, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+1+k, b, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h (a+1) b (d+1))
  ring_nf; finish

-- Main transition: (2n+3, 0, 0, 3n+3, 0) ⊢⁺ (2n+5, 0, 0, 3n+6, 0)
theorem main_trans (n : ℕ) : ⟨2*n+3, 0, 0, 3*n+3, 0⟩ [fm]⊢⁺ ⟨2*n+5, 0, 0, 3*n+6, 0⟩ := by
  -- Phase 1: R3 chain: (2n+3, 0, 0, 3n+3, 0) → (0, 0, 2n+3, 3n+3, 0)
  rw [show 2*n+3 = 0 + (2*n+3) from by ring]
  apply stepStar_stepPlus_stepPlus (a_to_c (2*n+3) 0 0)
  simp only [Nat.zero_add]
  -- Phase 2: R4 chain: (0, 0, 2n+3, 3n+3, 0) → (0, 0, 2n+3, 0, 3n+3)
  rw [show 3*n+3 = 0 + (3*n+3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (3*n+3) (2*n+3) 0 0)
  simp only [Nat.zero_add]
  -- Phase 3a: R5+R1+R1: (0, 0, 2n+3, 0, 3n+3) → (5, 0, 2n, 3, 3n+3)
  rw [show 2*n+3 = 2*n + 3 from by ring]
  apply stepStar_stepPlus_stepPlus r5r1r1
  -- Phase 3b: R2+R1 chain (2n rounds): (5, 0, 2n, 3, 3n+3) → (2n+5, 0, 0, 2n+3, n+3)
  rw [show (5 : ℕ) = 4+1 from by ring,
      show 2*n = 0 + 2*n from by ring,
      show 3*n+3 = (n+3) + 2*n from by ring]
  apply stepStar_stepPlus_stepPlus (r2r1_chain (2*n) 4 0 3 (n+3))
  rw [show 4+1+2*n = 2*n+5 from by ring,
      show 3+2*n = 2*n+3 from by ring]
  -- Phase 3c: R2 drain: (2n+5, 0, 0, 2n+3, n+3) → (n+2, n+3, 0, 2n+3, 0)
  rw [show 2*n+5 = (n+2) + (n+3) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (n+3) (n+2) 0 (2*n+3))
  simp only [Nat.zero_add]
  -- Phase 3d: R3+R1 chain: (n+2, n+3, 0, 2n+3, 0) → (2n+5, 0, 0, 3n+6, 0)
  rw [show n+2 = (n+1)+1 from by ring,
      show (n+3 : ℕ) = 0 + (n+3) from by ring,
      show 2*n+5 = (n+1)+1+(n+3) from by ring,
      show 3*n+6 = 2*n+3+(n+3) from by ring]
  apply stepStar_stepPlus (r3r1_chain (n+3) (n+1) 0 (2*n+3))
  simp [Q, Prod.mk.injEq]

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 3, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2*n+3, 0, 0, 3*n+3, 0⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩

