import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #954: [4/15, 33/14, 275/2, 91/11, 3/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  2  0  1  0
 0  0  0  1 -1  1
 0  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_954

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d, e+1, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- R4 drain: e into d and f.
theorem r4_drain : ∀ k, ∀ c d f, ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 1) (f + 1))
    ring_nf; finish

-- R1R2 chain: each round (R1, R2) consumes 1 c and 1 d, produces 1 a and 1 e.
theorem r1r2_chain : ∀ k, ∀ a c d e f, ⟨a, 1, c + k, d + k, e, f⟩ [fm]⊢* ⟨a + k, 1, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f)
    ring_nf; finish

-- R3 drain: a into c (×2) and e.
theorem r3_drain : ∀ k, ∀ c e f, ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 2) (e + 1) f)
    ring_nf; finish

-- R5+R1R2+R1: (0, 0, c+D+1, D, 0, f+1) →⁺ (D+2, 0, c, 0, D, f)
theorem r5_r1r2_r1 (c D f : ℕ) :
    ⟨0, 0, c + D + 1, D, 0, f + 1⟩ [fm]⊢⁺ ⟨D + 2, 0, c, 0, D, f⟩ := by
  -- R5 fires.
  step fm
  -- (0, 1, c+D+1, D, 0, f)
  -- R1R2 chain (D rounds).
  rw [show c + D + 1 = (c + 1) + D from by ring]
  -- Goal: (0, 1, (c+1)+D, D, 0, f) ⊢* (D+2, 0, c, 0, D, f)
  -- Use the chain with a helper rewrite.
  have h := r1r2_chain D 0 (c + 1) 0 0 f
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  -- (D, 1, c+1, 0, D, f) ⊢* (D+2, 0, c, 0, D, f)
  step fm
  finish

-- Main transition.
theorem main_trans (d E F : ℕ) :
    ⟨0, 0, E + d + 2, 0, E + 1, F⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 2 * E + d + 6, 0, 2 * E + 4, F + E⟩ := by
  -- Phase 1: R4 drain (E+1).
  apply stepStar_stepPlus_stepPlus (r4_drain (E + 1) (E + d + 2) 0 F)
  -- (0, 0, E+d+2, E+1, 0, F+E+1)
  rw [show (0 : ℕ) + (E + 1) = E + 1 from by ring,
      show F + (E + 1) = (F + E) + 1 from by ring,
      show E + d + 2 = d + (E + 1) + 1 from by ring]
  -- Phase 2: R5 + R1R2 chain + R1.
  apply stepPlus_stepStar_stepPlus (r5_r1r2_r1 d (E + 1) (F + E))
  -- (E+3, 0, d, 0, E+1, F+E)
  rw [show E + 1 + 2 = E + 3 from by ring]
  -- Phase 3: R3 drain (E+3).
  apply stepStar_trans (r3_drain (E + 3) d (E + 1) (F + E))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0 + 0 + 2, 0, 0 + 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨d, E, F⟩ ↦ ⟨0, 0, E + d + 2, 0, E + 1, F⟩) ⟨0, 0, 0⟩
  intro ⟨d, E, F⟩
  refine ⟨⟨d + 1, 2 * E + 3, F + E⟩, ?_⟩
  show ⟨0, 0, E + d + 2, 0, E + 1, F⟩ [fm]⊢⁺ ⟨0, 0, (2 * E + 3) + (d + 1) + 2, 0, (2 * E + 3) + 1, F + E⟩
  rw [show (2 * E + 3) + (d + 1) + 2 = 2 * E + d + 6 from by ring,
      show (2 * E + 3) + 1 = 2 * E + 4 from by ring]
  exact main_trans d E F

end Sz22_2003_unofficial_954
