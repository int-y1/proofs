import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #880: [4/15, 1029/2, 11/147, 5/7, 3/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  3  0
 0 -1  0 -2  1
 0  0  1 -1  0
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_880

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+3, e⟩
  | ⟨a, b+1, c, d+2, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R2 drain: (a+k, b, 0, d, e) →* (a, b+k, 0, d+3*k, e)
theorem r2_drain : ∀ k, ∀ a b d e, ⟨a + k, b, 0, d, e⟩ [fm]⊢* ⟨a, b + k, 0, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (d + 3) e)
    ring_nf; finish

-- R3 drain: (0, b+k, 0, d+2*k, e) →* (0, b, 0, d, e+k)
theorem r3_drain : ∀ k, ∀ b d e, ⟨0, b + k, 0, d + 2 * k, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring,
        show d + 2 * (k + 1) = d + 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 1))
    ring_nf; finish

-- R4 drain: (0, 0, c, d+k, e) →* (0, 0, c+k, d, e)
theorem r4_drain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R2R1 interleaved: (a+1, 0, c+k, d, e) →* (a+k+1, 0, c, d+3*k, e)
theorem r2r1_chain : ∀ k, ∀ a c d e, ⟨a + 1, 0, c + k, d, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c (d + 3) e)
    ring_nf; finish

-- Phase 3b: (0, 0, D+1, 0, E+1) ⊢⁺ (D+2, 0, 0, 3*D, E)
theorem phase3b (D E : ℕ) : ⟨0, 0, D + 1, 0, E + 1⟩ [fm]⊢⁺ ⟨D + 2, 0, 0, 3 * D, E⟩ := by
  step fm
  step fm
  -- after R5+R1: (2, 0, D, 0, E)
  -- need to show: (2, 0, D, 0, E) ⊢* (D+2, 0, 0, 3*D, E)
  -- Use r2r1_chain with a=1, c=0, k=D
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (D : ℕ) = 0 + D from by ring,
      show (0 : ℕ) = 0 + 3 * 0 from by ring]
  apply stepStar_trans (r2r1_chain D 1 0 (3 * 0) E)
  ring_nf; finish

-- Phases 1-3: (a+1, 0, 0, d, e) ⊢* (0, 0, d+a+1, 0, e+a+1)
theorem phases123 (a d e : ℕ) :
    ⟨a + 1, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, d + a + 1, 0, e + a + 1⟩ := by
  -- Phase 1: R2 drain
  rw [show a + 1 = 0 + (a + 1) from by ring]
  apply stepStar_trans (r2_drain (a + 1) 0 0 d e)
  -- After: (0, a+1, 0, d+3*(a+1), e)
  -- Phase 2: R3 drain
  rw [show d + 3 * (a + 1) = (d + a + 1) + 2 * (a + 1) from by ring,
      show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (r3_drain (a + 1) 0 (d + a + 1) e)
  -- After: (0, 0, 0, d+a+1, e+a+1)
  -- Phase 3: R4 drain
  rw [show d + a + 1 = 0 + (d + a + 1) from by ring]
  apply stepStar_trans (r4_drain (d + a + 1) 0 0 (e + (a + 1)))
  ring_nf; finish

-- Main transition.
theorem main_trans (a d e : ℕ) :
    ⟨a + 1, 0, 0, d, e⟩ [fm]⊢⁺ ⟨d + a + 2, 0, 0, 3 * (d + a), e + a⟩ := by
  apply stepStar_stepPlus_stepPlus (phases123 a d e)
  rw [show d + a + 1 = (d + a) + 1 from by ring,
      show e + a + 1 = (e + a) + 1 from by ring]
  exact phase3b (d + a) (e + a)

theorem nonhalt : ¬halts fm c₀ := by
  show ¬halts fm ⟨0 + 1, 0, 0, 0, 0⟩
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨a, d, e⟩ ↦ ⟨a + 1, 0, 0, d, e⟩) ⟨0, 0, 0⟩
  intro ⟨a, d, e⟩
  exact ⟨⟨d + a + 1, 3 * (d + a), e + a⟩, main_trans a d e⟩
