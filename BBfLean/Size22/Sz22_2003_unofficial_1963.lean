import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1963: [99/35, 1/66, 5/3, 4/5, 147/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  0  0 -1
 0 -1  1  0  0
 2  0 -1  0  0
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1963

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R1+R3 interleave: k rounds of (R1, R3).
theorem r1r3_chain : ∀ k b D e, ⟨(0 : ℕ), b, 1, k + D, e⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 1, D, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b D e
  · ring_nf; exists 0
  · rw [show (k + 1) + D = (k + D) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) D (e + 1))
    ring_nf; finish

-- Full R1+R3 chain plus final R1.
theorem r1r3_full : ∀ D, ⟨(0 : ℕ), 0, 1, D + 1, 0⟩ [fm]⊢* ⟨(0 : ℕ), D + 2, 0, 0, D + 1⟩ := by
  intro D
  apply stepStar_trans (r1r3_chain D 0 1 0)
  step fm
  ring_nf; finish

-- R3 chain: move b to c.
theorem r3_chain : ∀ k b c e, ⟨(0 : ℕ), b + k, c, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) e)
    ring_nf; finish

-- R4 chain: convert c to a.
theorem r4_chain : ∀ k a c e, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c e)
    ring_nf; finish

-- R5+R2 chain: drain a and e simultaneously, building d.
theorem r5r2_chain : ∀ k a d e, ⟨a + 2 * k, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + 2 * (k + 1) = (a + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih a (d + 2) e)
    ring_nf; finish

-- Main transition: (2, 0, 0, d+4, 0) ⊢⁺ (2, 0, 0, 2*d+10, 0).
-- Recurrence: d ↦ 2*d + 2 on the canonical family (2, 0, 0, d, 0).
theorem main_trans : ∀ d, ⟨2, 0, 0, d + 4, 0⟩ [fm]⊢⁺ ⟨(2 : ℕ), 0, 0, 2 * d + 10, 0⟩ := by
  intro d
  step fm
  step fm
  step fm
  step fm
  step fm
  rw [show d + 5 = (d + 4) + 1 from by ring]
  apply stepStar_trans (r1r3_full (d + 4))
  rw [show d + 4 + 2 = 0 + (d + 6) from by ring]
  apply stepStar_trans (r3_chain (d + 6) 0 0 (d + 4 + 1))
  apply stepStar_trans (r4_chain (d + 6) 0 0 (d + 4 + 1))
  rw [show 0 + 2 * (d + 6) = 2 + 2 * (d + 4 + 1) from by ring]
  have := r5r2_chain (d + 4 + 1) 2 0 0
  simp only [Nat.zero_add] at this
  convert this using 2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 4, 0⟩) (by execute fm 15)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨2, 0, 0, d + 4, 0⟩) 0
  intro d; exists (2 * d + 6)
  exact main_trans d
