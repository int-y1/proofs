import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #70: [1/18, 2/35, 7865/2, 21/11, 2/39]

Vector representation:
```
-1 -2  0  0  0  0
 1  0 -1 -1  0  0
-1  0  1  0  2  1
 0  1  0  1 -1  0
 1 -1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_70

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+2, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- Phase 1: R4 chain. Convert e to b and d.
theorem r4_chain : ∀ k b d e f, ⟨0, b, 0, d, e+k, f⟩ [fm]⊢* ⟨0, b+k, 0, d+k, e, f⟩ := by
  intro k; induction' k with k h <;> intro b d e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Phase 2: R5+R1 interleaved chain. Drain b and f in pairs.
theorem r5r1_chain : ∀ k b d f, ⟨0, b+3*k+2, 0, d, 0, f+k⟩ [fm]⊢* ⟨0, b+2, 0, d, 0, f⟩ := by
  intro k; induction' k with k h <;> intro b d f
  · exists 0
  rw [show b + 3 * (k + 1) + 2 = (b + 3 * k + 2) + 3 from by ring,
      show f + (k + 1) = (f + k) + 1 from by ring]
  step fm  -- R5: (1, b+3k+4, 0, d, 0, f+k)
  step fm  -- R1: (0, b+3k+2, 0, d, 0, f+k)
  exact h _ _ _

-- Final R5 after Phase 2 draining.
theorem final_r5 : ⟨0, b+2, 0, d, 0, f+1⟩ [fm]⊢* ⟨1, b+1, 0, d, 0, f⟩ := by
  step fm; finish

-- Phase 4: R2+R3 interleaved chain.
theorem r2r3_chain : ∀ k d e f, ⟨0, 1, 1, d+k, e, f⟩ [fm]⊢* ⟨0, 1, 1, d, e+2*k, f+k⟩ := by
  intro k; induction' k with k h <;> intro d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm  -- R2: (1, 1, 0, d+k, e, f)
  step fm  -- R3: (0, 1, 1, d+k, e+2, f+1)
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: C(g) ⊢⁺ C(2g+1)
-- C(g) = (0, 0, 0, 0, 3g+2, 2g+2)
theorem main_trans (g : ℕ) :
    ⟨0, 0, 0, 0, 3*g+2, 2*g+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 0, 6*g+5, 4*g+4⟩ := by
  -- Phase 1: R4 chain (3g+2 times)
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (3*g+2) 0 0 0 (2*g+2)
    simp only [Nat.zero_add] at h; exact h
  -- Now at (0, 3g+2, 0, 3g+2, 0, 2g+2)
  -- Phase 2: R5+R1 chain (g pairs)
  apply stepStar_stepPlus_stepPlus
  · have h := r5r1_chain g 0 (3*g+2) (g+2)
    simp only [Nat.zero_add, (by ring : g + 2 + g = 2 * g + 2)] at h; exact h
  -- Now at (0, 2, 0, 3g+2, 0, g+2)
  -- Final R5
  apply stepStar_stepPlus_stepPlus
  · have h := @final_r5 0 (3*g+2) (g+1)
    simp only [Nat.zero_add, (by ring : g + 1 + 1 = g + 2)] at h; exact h
  -- Now at (1, 1, 0, 3g+2, 0, g+1)
  -- Phase 3: R3 single step
  step fm
  -- Now at (0, 1, 1, 3g+2, 2, g+2)
  -- Phase 4: R2+R3 chain (3g+2 times)
  show ⟨0, 1, 1, 3 * g + 2, 2, g + 2⟩ [fm]⊢* ⟨0, 0, 0, 0, 6 * g + 5, 4 * g + 4⟩
  apply stepStar_trans
  · have h := r2r3_chain (3*g+2) 0 2 (g+2)
    simp only [Nat.zero_add,
               (by ring : 2 + 2 * (3 * g + 2) = 6 * g + 6),
               (by ring : g + 2 + (3 * g + 2) = 4 * g + 4)] at h; exact h
  -- Now at (0, 1, 1, 0, 6g+6, 4g+4)
  -- Phase 5: R4, R2, R1 (3 closing steps)
  step fm  -- R4: (0, 2, 1, 1, 6g+5, 4g+4)
  step fm  -- R2: (1, 2, 0, 0, 6g+5, 4g+4)
  step fm  -- R1: (0, 0, 0, 0, 6g+5, 4g+4)
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun g ↦ ⟨0, 0, 0, 0, 3*g+2, 2*g+2⟩) 0
  intro g; exists 2*g+1
  show ⟨0, 0, 0, 0, 3*g+2, 2*g+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 0, 3*(2*g+1)+2, 2*(2*g+1)+2⟩
  simp only [(by ring : 3 * (2 * g + 1) + 2 = 6 * g + 5),
             (by ring : 2 * (2 * g + 1) + 2 = 4 * g + 4)]
  exact main_trans g

end Sz22_2003_unofficial_70
