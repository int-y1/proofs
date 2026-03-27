import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #71: [1/18, 22/35, 65/2, 147/13, 2/33]

Vector representation:
```
-1 -2  0  0  0  0
 1  0 -1 -1  1  0
-1  0  1  0  0  1
 0  1  0  2  0 -1
 1 -1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_71

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+2, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- R3/R2 chain: (1,0,0,d+k,e,f) ⊢* (1,0,0,d,e+k,f+k)
theorem r3r2_chain : ∀ k, ∀ d e f,
    ⟨1, 0, 0, d + k, e, f⟩ [fm]⊢* ⟨1, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k h <;> intro d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h d (e + 1) (f + 1))
  ring_nf; finish

-- R4 chain: (0,b,c,d,e,f+k) ⊢* (0,b+k,c,d+2*k,e,f)
theorem r4_chain : ∀ k, ∀ b d e f,
    ⟨0, b, 0, d, e, f + k⟩ [fm]⊢* ⟨0, b + k, 0, d + 2*k, e, f⟩ := by
  intro k; induction' k with k h <;> intro b d e f
  · simp; exists 0
  rw [show f + (k + 1) = (f + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h (b + 1) (d + 2) e f)
  ring_nf; finish

-- R5/R1 drain: (0,3k+1,0,D,e+k,0) ⊢* (0,1,0,D,e,0)
theorem r5r1_drain : ∀ k, ∀ D e,
    ⟨0, 3*k + 1, 0, D, e + k, 0⟩ [fm]⊢* ⟨0, 1, 0, D, e, 0⟩ := by
  intro k; induction' k with k h <;> intro D e
  · simp; exists 0
  rw [show 3 * (k + 1) + 1 = (3 * k + 1) + 3 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h D e)
  ring_nf; finish

-- Main transition: C(n) ⊢⁺ C(2n+1)
-- where C(n) = (1, 0, 0, 3n, 2n, 0)
theorem main_trans (n : ℕ) :
    ⟨1, 0, 0, 3*n, 2*n, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 6*n + 3, 4*n + 2, 0⟩ := by
  -- Phase 1: R3/R2 chain (3n rounds)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 0, 0, 0, 5*n, 3*n⟩)
  · have h := r3r2_chain (3*n) 0 (2*n) 0
    simp only [Nat.zero_add] at h
    rw [show 2 * n + 3 * n = 5 * n from by ring] at h
    exact h
  -- Phase 2: R3 step
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 1, 0, 5*n, 3*n + 1⟩)
  · step fm; finish
  -- Phase 3: 8 fixed steps (R4, R2, R3, R2, R3, R4, R2, R1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 1, 5*n + 3, 3*n + 1⟩)
  · step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
    ring_nf; finish
  -- Phase 4: R4 chain (3n+1 rounds)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3*n + 1, 0, 6*n + 3, 5*n + 3, 0⟩)
  · rw [show 3 * n + 1 = 0 + (3 * n + 1) from by ring,
        show 6 * n + 3 = 1 + 2 * (3 * n + 1) from by ring]
    exact r4_chain (3*n + 1) 0 1 (5*n + 3) 0
  -- Phase 5: R5/R1 drain (n rounds)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 0, 6*n + 3, 4*n + 3, 0⟩)
  · rw [show 3 * n + 1 = 3 * n + 1 from rfl,
        show 5 * n + 3 = (4 * n + 3) + n from by ring]
    exact r5r1_drain n (6*n + 3) (4*n + 3)
  -- Phase 6: R5 step
  rw [show 4 * n + 3 = (4 * n + 2) + 1 from by ring]
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, 3*n, 2*n, 0⟩) 0
  intro n; exact ⟨2*n + 1, by
    show ⟨1, 0, 0, 3*n, 2*n, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 3*(2*n + 1), 2*(2*n + 1), 0⟩
    rw [show 3 * (2 * n + 1) = 6 * n + 3 from by ring,
        show 2 * (2 * n + 1) = 4 * n + 2 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_71
