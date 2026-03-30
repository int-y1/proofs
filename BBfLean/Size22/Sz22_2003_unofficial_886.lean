import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #886: [4/15, 147/2, 11/3, 5/77, 3/7, 1/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  2  0
 0 -1  0  0  1
 0  0  1 -1 -1
 0  1  0 -1  0
 0  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_886

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- Phase 1 (R2 chain): drain a to b, adding 2 per step to d.
theorem r2_chain : ∀ k b d, (⟨a + k, b, 0, d, 0⟩ : Q) [fm]⊢* ⟨a, b + k, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih (b + 1) (d + 2))
  ring_nf; finish

-- Phase 2 (R3 chain): drain b to e.
theorem r3_chain : ∀ k d e, (⟨0, b + k, 0, d, e⟩ : Q) [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih d (e + 1))
  ring_nf; finish

-- Phase 3 (R4 chain): convert d,e pairs to c.
theorem r4_chain : ∀ k c, (⟨0, 0, c, d + k, k⟩ : Q) [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    show (⟨0, 0, c, (d + k) + 1, k + 1⟩ : Q) [fm]⊢* _
    step fm
    apply stepStar_trans (ih (c + 1))
    ring_nf; finish

-- Phase 4 interleave: (a, 1, c+1, D, 0) ->* (a+c+2, 0, 0, D+2*c, 0)
theorem interleave : ∀ k a D, (⟨a, 1, k + 1, D, 0⟩ : Q) [fm]⊢* ⟨a + k + 2, 0, 0, D + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a D
  · step fm; finish
  rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (ih (a + 1) (D + 2))
  ring_nf; finish

-- Main transition: (a+3, 0, 0, d, 0) ->+ (a+4, 0, 0, d+3*(a+2), 0)
theorem main_trans (a d : ℕ) : (⟨a + 3, 0, 0, d, 0⟩ : Q) [fm]⊢⁺ ⟨a + 4, 0, 0, d + 3 * (a + 2), 0⟩ := by
  -- Phase 1: R2 chain
  have phase1 : (⟨a + 3, 0, 0, d, 0⟩ : Q) [fm]⊢* ⟨0, a + 3, 0, d + 2 * (a + 3), 0⟩ := by
    have h := @r2_chain 0 (a + 3) 0 d
    simpa using h
  have phase2 : (⟨0, a + 3, 0, d + 2 * (a + 3), 0⟩ : Q) [fm]⊢* ⟨0, 0, 0, d + 2 * (a + 3), a + 3⟩ := by
    have h := @r3_chain 0 (a + 3) (d + 2 * (a + 3)) 0
    simpa using h
  have phase3 : (⟨0, 0, 0, d + 2 * (a + 3), a + 3⟩ : Q) [fm]⊢* ⟨0, 0, a + 3, d + (a + 3), 0⟩ := by
    rw [show d + 2 * (a + 3) = (d + (a + 3)) + (a + 3) from by ring]
    have h := @r4_chain (d + (a + 3)) (a + 3) 0
    rwa [Nat.zero_add] at h
  -- Phase 4: R5 + interleave
  have phase4 : (⟨0, 0, a + 3, d + (a + 3), 0⟩ : Q) [fm]⊢⁺ ⟨a + 4, 0, 0, d + 3 * (a + 2), 0⟩ := by
    rw [show d + (a + 3) = (d + (a + 2)) + 1 from by ring,
        show (a : ℕ) + 3 = (a + 2) + 1 from by ring]
    step fm
    apply stepStar_trans (interleave (a + 2) 0 (d + (a + 2)))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus (stepStar_trans (stepStar_trans phase1 phase2) phase3) phase4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 3, 0⟩)
  · execute fm 15
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 3, 0, 0, d, 0⟩) ⟨0, 3⟩
  intro ⟨a, d⟩
  exact ⟨⟨a + 1, d + 3 * (a + 2)⟩, main_trans a d⟩
