import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1525: [7/30, 12/77, 33/2, 5/11, 14/3]

Vector representation:
```
-1 -1 -1  1  0
 2  1  0 -1 -1
-1  1  0  0  1
 0  0  1  0 -1
 1 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1525

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Phase 1: R3 drain a into b and e (c=0, d=0).
theorem r3_drain : ∀ k b e, ⟨k, b, 0, 0, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih
  · intro b e; exists 0
  · intro b e; step fm
    apply stepStar_trans (ih (b + 1) (e + 1)); ring_nf; finish

-- Phase 2: R4 drain e into c (a=0, d=0).
theorem r4_drain : ∀ k b c, ⟨0, b, c, 0, k⟩ [fm]⊢* ⟨0, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih
  · intro b c; exists 0
  · intro b c; step fm
    apply stepStar_trans (ih b (c + 1)); ring_nf; finish

-- Phase 3: R5/R1 chain (drains c, transfers b to d).
theorem r5r1_chain : ∀ k b d, ⟨0, b + 2 * k, k, d, 0⟩ [fm]⊢* ⟨0, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro b d; exists 0
  · intro b d
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih b (d + 2)); ring_nf; finish

-- Phase 5: R3/R2 chain (drains d, builds a and b).
theorem r3r2_chain : ∀ k a b, ⟨a + 1, b, 0, k, 0⟩ [fm]⊢* ⟨a + k + 1, b + 2 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih
  · intro a b; exists 0
  · intro a b
    rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 2)); ring_nf; finish

-- Main transition: (a+1, a+F+2, 0, 0, 0) ⊢⁺ (2a+4, 4a+F+6, 0, 0, 0)
theorem main_trans (a F : ℕ) :
    ⟨a + 1, a + F + 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * a + 4, 4 * a + F + 6, 0, 0, 0⟩ := by
  -- Phase 1: first R3 step to establish ⊢⁺, then drain remaining a
  step fm
  rw [show a + F + 2 + 1 = a + F + 3 from by ring]
  apply stepStar_trans (r3_drain a (a + F + 3) 1)
  -- Now at (0, 2a+F+3, 0, 0, a+1)
  rw [show a + F + 3 + a = 2 * a + F + 3 from by ring,
      show 1 + a = a + 1 from by ring]
  -- Phase 2: R4 drain a+1 steps
  apply stepStar_trans (r4_drain (a + 1) (2 * a + F + 3) 0)
  -- Now at (0, 2a+F+3, a+1, 0, 0)
  rw [show (0 + (a + 1) : ℕ) = a + 1 from by ring,
      show 2 * a + F + 3 = (F + 1) + 2 * (a + 1) from by ring]
  -- Phase 3: R5/R1 chain, a+1 pairs
  apply stepStar_trans (r5r1_chain (a + 1) (F + 1) 0)
  -- Now at (0, F+1, 0, 2a+2, 0)
  rw [show 0 + 2 * (a + 1) = 2 * a + 2 from by ring]
  -- Phase 4: R5 once
  step fm
  -- Now at (1, F, 0, 2a+3, 0)
  rw [show 2 * a + 1 + 1 + 1 = 2 * a + 3 from by ring]
  -- Phase 5: R3/R2 chain, 2a+3 steps
  apply stepStar_trans (r3r2_chain (2 * a + 3) 0 F)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 3, 0, 0, 0⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + 1, p.1 + p.2 + 2, 0, 0, 0⟩) ⟨1, 0⟩
  intro ⟨a, F⟩
  exact ⟨⟨2 * a + 3, 2 * a + F + 1⟩, by
    show ⟨a + 1, a + F + 2, 0, 0, 0⟩ [fm]⊢⁺
      ⟨(2 * a + 3) + 1, (2 * a + 3) + (2 * a + F + 1) + 2, 0, 0, 0⟩
    rw [show (2 * a + 3) + 1 = 2 * a + 4 from by ring,
        show (2 * a + 3) + (2 * a + F + 1) + 2 = 4 * a + F + 6 from by ring]
    exact main_trans a F⟩

end Sz22_2003_unofficial_1525
