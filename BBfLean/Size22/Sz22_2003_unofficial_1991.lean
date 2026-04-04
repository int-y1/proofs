import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1991: [99/35, 5/39, 338/5, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  1  0
 0 -1  1  0  0 -1
 1  0 -1  0  0  2
 0  0  0  1 -1  0
-1  0  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1991

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+2⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | _ => none

-- R3 chain: drain c into a and f.
theorem r3_chain : ∀ k, ⟨a, 0, k, 0, e, f⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e, f + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a e f
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show f + 2 * (k + 1) = (f + 2) + 2 * k from by ring]
    step fm
    exact ih

-- R4 chain: move e to d.
theorem r4_chain : ∀ k, ⟨a, 0, 0, d, k, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0, f⟩ := by
  intro k; induction' k with k ih generalizing a d f
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih

-- R2 chain: drain b and f into c.
theorem r2_chain : ∀ k, ⟨a, k, c, 0, e, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e, 0⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show c + (k + 1) = (c + 1) + k from by ring]
    step fm
    exact ih

-- Interleaving phase: R1+R2 pairs followed by R2 drain.
theorem interleave : ∀ d, ∀ b, ⟨a, b, 1, d + 1, b + 1, 2 * d + b + 2⟩ [fm]⊢*
    ⟨a, 0, b + d + 2, 0, b + d + 2, 0⟩ := by
  intro d; induction' d with d ih generalizing a
  · intro b
    step fm
    rw [show 2 * 0 + b + 2 = (b + 2) from by ring,
        show b + 0 + 2 = b + 2 from by ring]
    apply stepStar_trans (r2_chain (b + 2) (a := a) (c := 0) (e := b + 2))
    ring_nf; finish
  · intro b
    rw [show 2 * (d + 1) + b + 2 = 2 * d + (b + 1) + 2 + 1 from by ring]
    step fm
    rw [show 2 * d + (b + 1) + 2 = 2 * d + b + 3 from by ring]
    step fm
    rw [show 2 * d + b + 3 = 2 * d + (b + 1) + 2 from by ring]
    apply stepStar_trans (ih (b := b + 1))
    rw [show b + 1 + d + 2 = b + (d + 1) + 2 from by ring]
    finish

-- Main transition: one canonical step.
theorem main_trans : ⟨a, 0, n + 1, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨a + n, 0, n + 2, 0, n + 2, 0⟩ := by
  -- Phase 1: R3 chain (n+1 times)
  apply stepStar_stepPlus_stepPlus
  · exact r3_chain (n + 1) (a := a) (e := n + 1) (f := 0)
  -- Now at (a+n+1, 0, 0, 0, n+1, 2*(n+1))
  apply stepStar_stepPlus_stepPlus
  · rw [show 0 + 2 * (n + 1) = 2 * n + 2 from by ring]
    exact r4_chain (n + 1) (a := a + n + 1) (d := 0) (f := 2 * n + 2)
  -- Now at (a+n+1, 0, 0, n+1, 0, 2n+2)
  rw [show 0 + (n + 1) = n + 1 from by ring]
  -- R5 step
  apply step_stepStar_stepPlus
  · show fm ⟨(a + n) + 1, 0, 0, n + 1, 0, 2 * n + 2⟩ = some ⟨a + n, 0, 1, n + 1, 1, 2 * n + 2⟩
    simp [fm]
  -- Now at (a+n, 0, 1, n+1, 1, 2n+2)
  rw [show n + 1 = n + 0 + 1 from by ring,
      show (2 : ℕ) * n + 2 = 2 * n + 0 + 2 from by ring]
  apply stepStar_trans (interleave n (b := 0) (a := a + n))
  rw [show 0 + n + 2 = n + 2 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 2, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a, 0, n + 2, 0, n + 2, 0⟩) ⟨0, 0⟩
  intro ⟨a, n⟩; exact ⟨⟨a + n + 1, n + 1⟩, main_trans⟩
