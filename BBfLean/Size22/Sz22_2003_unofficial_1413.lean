import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1413: [7/15, 117/77, 50/7, 11/13, 91/2]

Vector representation:
```
 0 -1 -1  1  0  0
 0  2  0 -1 -1  1
 1  0  2 -1  0  0
 0  0  0  0  1 -1
-1  0  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1413

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a, b+2, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a+1, b, c+2, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | _ => none

-- Phase 1: R3 chain. Drain d, producing c and incrementing a.
theorem r3_chain : ∀ k, ⟨a, 0, c, d + k, 0, f⟩ [fm]⊢* ⟨a + k, 0, c + 2 * k, d, 0, f⟩ := by
  intro k; induction' k with k ih generalizing a c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (c := c + 2))
    ring_nf; finish

-- Phase 2: R4 chain. Drain f, producing e.
theorem r4_chain : ∀ k, ⟨a, 0, c, 0, e, f + k⟩ [fm]⊢* ⟨a, 0, c, 0, e + k, f⟩ := by
  intro k; induction' k with k ih generalizing e f
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 1))
    ring_nf; finish

-- Phase 4: Interleaved R2/R1/R1 chain.
theorem interleaved : ∀ k, ⟨a, 0, 2 * (k + 1), d + 1, k + 1, f⟩ [fm]⊢*
    ⟨a, 0, 0, d + 1 + (k + 1), 0, f + (k + 1)⟩ := by
  intro k; induction' k with k ih generalizing d f
  · -- k = 0: one round of R2, R1, R1
    step fm; step fm; step fm; ring_nf; finish
  · -- k+1: (a, 0, 2*(k+2), d+1, k+2, f)
    rw [show 2 * (k + 1 + 1) = 2 * (k + 1) + 2 from by ring,
        show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    step fm  -- R1
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 1) (f := f + 1))
    ring_nf; finish

-- Main transition: (a, 0, 0, d+2, 0, d+2) →⁺ (a+d+1, 0, 0, d+3, 0, d+3)
theorem main_trans : ⟨a, 0, 0, d + 2, 0, d + 2⟩ [fm]⊢⁺ ⟨a + d + 1, 0, 0, d + 3, 0, d + 3⟩ := by
  -- Phase 1: R3 chain with k = d+2
  have h1 : ⟨a, 0, 0, d + 2, 0, d + 2⟩ [fm]⊢*
      ⟨a + (d + 2), 0, 2 * (d + 2), 0, 0, d + 2⟩ := by
    rw [show (d + 2 : ℕ) = 0 + (d + 2) from by ring]
    apply stepStar_trans (r3_chain (d + 2) (a := a) (c := 0) (d := 0) (f := 0 + (d + 2)))
    ring_nf; finish
  -- Phase 2: R4 chain with k = d+2
  have h2 : ⟨a + (d + 2), 0, 2 * (d + 2), 0, 0, d + 2⟩ [fm]⊢*
      ⟨a + (d + 2), 0, 2 * (d + 2), 0, d + 2, 0⟩ := by
    rw [show (d + 2 : ℕ) = 0 + (d + 2) from by ring]
    apply stepStar_trans (r4_chain (d + 2) (a := a + (0 + (d + 2))) (c := 2 * (0 + (d + 2))) (e := 0) (f := 0))
    ring_nf; finish
  -- Phase 3: R5 step + Phase 4: interleaved
  have h34 : ⟨a + (d + 2), 0, 2 * (d + 2), 0, d + 2, 0⟩ [fm]⊢⁺
      ⟨a + d + 1, 0, 0, d + 3, 0, d + 3⟩ := by
    rw [show a + (d + 2) = (a + d + 1) + 1 from by ring]
    step fm
    show ⟨a + d + 1, 0, 2 * (d + 1 + 1), 0 + 1, d + 1 + 1, 1⟩ [fm]⊢* _
    apply stepStar_trans (interleaved (d + 1) (a := a + d + 1) (d := 0) (f := 1))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1 (stepStar_stepPlus_stepPlus h2 h34)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a, 0, 0, d + 2, 0, d + 2⟩) ⟨0, 0⟩
  intro ⟨a, d⟩; exact ⟨⟨a + d + 1, d + 1⟩, main_trans⟩
