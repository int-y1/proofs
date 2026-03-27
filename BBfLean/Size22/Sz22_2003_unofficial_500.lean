import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #500: [28/15, 3/22, 25/2, 121/7, 6/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  2
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_500

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- Canonical form: (0, 0, 2*d + 2*n + 6, d + 1, 0)
-- Transition: (n, d) → (n + 1, 2*d + 2)

-- Phase 1: R4 drain d to e
theorem d_to_e : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + 2 * k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h c d (e + 2))
  ring_nf; finish

-- Phase 2: Interleaved R2/R1 chain
-- Each round: R2 (a+1,0,c,d,e+1) → (a,1,c,d,e), then R1 (a,1,c+1,d,e) → (a+2,0,c,d+1,e)
theorem r2r1_chain : ∀ k, ∀ A C D E, ⟨A + 1, 0, C + k, D, E + k⟩ [fm]⊢* ⟨A + 1 + k, 0, C, D + k, E⟩ := by
  intro k; induction' k with k h <;> intro A C D E
  · exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  -- State: (A+1, 0, (C+k)+1, D, (E+k)+1)
  -- R2: matches (a+1, b, c, d, e+1) with a=A, b=0, c=(C+k)+1, d=D, e=E+k
  -- Result: (A, 0+1, (C+k)+1, D, E+k)
  step fm
  -- State: (A, 1, (C+k)+1, D, E+k)
  -- R1: matches (a, b+1, c+1, d, e) with a=A, b=0, c=C+k, d=D, e=E+k
  -- Result: (A+2, 0, C+k, D+1, E+k)
  step fm
  -- State: (A+2, 0, C+k, D+1, E+k)
  rw [show A + 2 = (A + 1) + 1 from by ring]
  apply stepStar_trans (h (A + 1) C (D + 1) E)
  ring_nf; finish

-- Phase 3: R3 drain a
theorem a_drain : ∀ k, ∀ a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h a (c + 2) d)
  ring_nf; finish

-- Main transition: (0, 0, 2d+2n+6, d+1, 0) ⊢⁺ (0, 0, 4d+2n+12, 2d+3, 0)
theorem main_trans (n d : ℕ) : ⟨0, 0, 2 * d + 2 * n + 6, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 4 * d + 2 * n + 12, 2 * d + 3, 0⟩ := by
  -- Phase 1: R4 × (d+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2 * d + 2 * n + 6, 0, 2 * d + 2⟩)
  · have h := d_to_e (d + 1) (2 * d + 2 * n + 6) 0 0
    simp only [Nat.zero_add] at h
    convert h using 2
  -- Phase 2: R5: (0, 0, 2d+2n+6, 0, 2d+2) → (1, 1, 2d+2n+5, 0, 2d+2)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 1, 2 * d + 2 * n + 5, 0, 2 * d + 2⟩)
  · show fm ⟨0, 0, (2 * d + 2 * n + 5) + 1, 0, 2 * d + 2⟩ = some ⟨0 + 1, 0 + 1, 2 * d + 2 * n + 5, 0, 2 * d + 2⟩
    simp [fm]
  -- Phase 3: R1: (1, 1, 2d+2n+5, 0, 2d+2) → (3, 0, 2d+2n+4, 1, 2d+2)
  apply stepStar_trans (c₂ := ⟨3, 0, 2 * d + 2 * n + 4, 1, 2 * d + 2⟩)
  · apply step_stepStar
    show fm ⟨1, 0 + 1, (2 * d + 2 * n + 4) + 1, 0, 2 * d + 2⟩ = some ⟨1 + 2, 0, 2 * d + 2 * n + 4, 0 + 1, 2 * d + 2⟩
    simp [fm]
  -- Phase 4: R2/R1 chain × (2d+1)
  apply stepStar_trans (c₂ := ⟨2 * d + 4, 0, 2 * n + 3, 2 * d + 2, 1⟩)
  · have h := r2r1_chain (2 * d + 1) 2 (2 * n + 3) 1 1
    convert h using 2; ring_nf
  -- Phase 5: R2: (2d+4, 0, 2n+3, 2d+2, 1) → (2d+3, 1, 2n+3, 2d+2, 0)
  apply stepStar_trans (c₂ := ⟨2 * d + 3, 1, 2 * n + 3, 2 * d + 2, 0⟩)
  · apply step_stepStar
    show fm ⟨(2 * d + 3) + 1, 0, 2 * n + 3, 2 * d + 2, 0 + 1⟩ = some ⟨2 * d + 3, 0 + 1, 2 * n + 3, 2 * d + 2, 0⟩
    simp [fm]
  -- Phase 6: R1: (2d+3, 1, 2n+3, 2d+2, 0) → (2d+5, 0, 2n+2, 2d+3, 0)
  apply stepStar_trans (c₂ := ⟨2 * d + 5, 0, 2 * n + 2, 2 * d + 3, 0⟩)
  · apply step_stepStar
    show fm ⟨2 * d + 3, 0 + 1, (2 * n + 2) + 1, 2 * d + 2, 0⟩ = some ⟨(2 * d + 3) + 2, 0, 2 * n + 2, (2 * d + 2) + 1, 0⟩
    simp [fm]
  -- Phase 7: R3 × (2d+5)
  have h := a_drain (2 * d + 5) 0 (2 * n + 2) (2 * d + 3)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 6, 1, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, d⟩ ↦ ⟨0, 0, 2 * d + 2 * n + 6, d + 1, 0⟩) ⟨0, 0⟩
  intro ⟨n, d⟩; exact ⟨⟨n + 1, 2 * d + 2⟩, by
    show ⟨0, 0, 2 * d + 2 * n + 6, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * (2 * d + 2) + 2 * (n + 1) + 6, (2 * d + 2) + 1, 0⟩
    have h := main_trans n d
    convert h using 2; ring_nf⟩

end Sz22_2003_unofficial_500
