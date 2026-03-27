import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #276: [14/15, 3/77, 25/7, 121/25, 21/2]

Vector representation:
```
 1 -1 -1  1  0
 0  1  0 -1 -1
 0  0  2 -1  0
 0  0 -2  0  2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_276

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Helper lemmas for steps that can't reduce with symbolic arguments
lemma step_r5 (b : ℕ) : ⟨1, b, 0, 0, 0⟩ [fm]⊢ ⟨0, b+1, 0, 1, 0⟩ := by
  cases b <;> rfl

lemma step_r3_d (a c d : ℕ) : ⟨a, 0, c, d+1, 0⟩ [fm]⊢ ⟨a, 0, c+2, d, 0⟩ := by
  cases a <;> cases c <;> rfl

lemma step_r4_c (a c e : ℕ) : ⟨a, 0, c+2, 0, e⟩ [fm]⊢ ⟨a, 0, c, 0, e+2⟩ := by
  cases a <;> cases c <;> rfl

lemma step_r3_init (k : ℕ) : ⟨0, 2*k+1, 0, 1, 0⟩ [fm]⊢ ⟨0, 2*k+1, 2, 0, 0⟩ := by
  cases k <;> rfl

-- R1+R3 chain
theorem chain_r1r3 (k : ℕ) : ⟨A, 2*k+1, 2, D, 0⟩ [fm]⊢* ⟨A+2*k+1, 0, 1, D+k+1, 0⟩ := by
  induction k generalizing A D with
  | zero => step fm; ring_nf; finish
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A := A + 2) (D := D + 1))
    ring_nf; finish

-- R3 chain: convert d to c
theorem chain_r3 (k : ℕ) : ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  induction k generalizing c d with
  | zero => finish
  | succ k ih =>
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    refine stepStar_trans (step_stepStar (step_r3_d a c (d + k))) ?_
    show ⟨a, 0, c + 2, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * (k + 1), d, 0⟩
    rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    exact ih (c := c + 2) (d := d)

-- R4 chain: convert c to e
theorem chain_r4 (k : ℕ) : ⟨a, 0, c+2*k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+2*k⟩ := by
  induction k generalizing e with
  | zero => finish
  | succ k ih =>
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    refine stepStar_trans (step_stepStar (step_r4_c a (c + 2*k) e)) ?_
    show ⟨a, 0, c + 2 * k, 0, e + 2⟩ [fm]⊢* ⟨a, 0, c, 0, e + 2 * (k + 1)⟩
    rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    exact ih (e := e + 2)

-- R5+R2 drain
theorem drain (k : ℕ) : ⟨a+k, b, 0, 0, k⟩ [fm]⊢* ⟨a, b+2*k, 0, 0, 0⟩ := by
  induction k generalizing a b with
  | zero => finish
  | succ k ih =>
    rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm; step fm
    show ⟨a + k, b + 1 + 1, 0, 0, k⟩ [fm]⊢* ⟨a, b + 2 * (k + 1), 0, 0, 0⟩
    rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show b + 1 + 1 = b + 2 from by ring]
    exact ih (a := a) (b := b + 2)

-- Main cycle
theorem cycle (k : ℕ) : ⟨1, 2*k, 0, 0, 0⟩ [fm]⊢⁺ ⟨1, 4*k+2, 0, 0, 0⟩ := by
  -- Phase 1: R5 -> (0, 2k+1, 0, 1, 0), R3 -> (0, 2k+1, 2, 0, 0)
  apply step_stepStar_stepPlus (step_r5 (2*k))
  refine stepStar_trans (step_stepStar (step_r3_init k)) ?_
  -- Phase 2: R1+R3 chain -> (2k+1, 0, 1, k+1, 0)
  refine stepStar_trans (chain_r1r3 k (A := 0) (D := 0)) ?_
  show ⟨0 + 2*k+1, 0, 1, 0+k+1, 0⟩ [fm]⊢* ⟨1, 4 * k + 2, 0, 0, 0⟩
  rw [show 0 + 2*k+1 = 2*k+1 from by ring, show 0+k+1 = k+1 from by ring]
  -- Phase 3: R3 chain -> (2k+1, 0, 2k+3, 0, 0)
  rw [show k + 1 = 0 + (k + 1) from by ring]
  refine stepStar_trans (chain_r3 (k + 1) (a := 2*k+1) (c := 1) (d := 0)) ?_
  show ⟨2*k+1, 0, 1 + 2*(k+1), 0, 0⟩ [fm]⊢* ⟨1, 4 * k + 2, 0, 0, 0⟩
  -- Phase 4: R4 chain -> (2k+1, 0, 1, 0, 2k+2)
  refine stepStar_trans (chain_r4 (k + 1) (a := 2*k+1) (c := 1) (e := 0)) ?_
  show ⟨2*k+1, 0, 1, 0, 0 + 2*(k+1)⟩ [fm]⊢* ⟨1, 4 * k + 2, 0, 0, 0⟩
  rw [show 0 + 2*(k+1) = 2*k+2 from by ring]
  -- Phase 5: R5, R1
  step fm; step fm
  -- Phase 6: R2, R2
  step fm; step fm
  -- Phase 7: drain
  show ⟨2 * k + 1, 2, 0, 0, 2 * k⟩ [fm]⊢* ⟨1, 4 * k + 2, 0, 0, 0⟩
  rw [show 2 * k + 1 = 1 + 2 * k from by ring,
      show 4 * k + 2 = 2 + 2 * (2 * k) from by ring]
  exact drain (2*k) (a := 1) (b := 2)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩)
  · finish
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k, q = ⟨1, 2*k, 0, 0, 0⟩)
  · intro c ⟨k, hk⟩; subst hk
    refine ⟨⟨1, 4*k+2, 0, 0, 0⟩, ⟨2*k+1, ?_⟩, cycle k⟩
    show (1, 4*k+2, 0, 0, 0) = (1, 2*(2*k+1), 0, 0, 0)
    ring_nf
  · exact ⟨0, rfl⟩
