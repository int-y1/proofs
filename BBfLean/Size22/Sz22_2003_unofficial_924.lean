import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #924: [4/15, 33/14, 25/2, 49/11, 14/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  2 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_924

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Phase: R2/R1 interleaved chain
-- From (a+1, 0, k, k, e) to (a+k+1, 0, 0, 0, e+k)
theorem r2r1_chain : ∀ k, ∀ a e,
    ⟨a + 1, 0, k, k, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1)); ring_nf; finish

-- Phase: R3 drain
-- From (k, 0, c, 0, e) to (0, 0, c+2*k, 0, e)
theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) e); ring_nf; finish

-- Phase: R4 drain
-- From (0, 0, c, d, k) to (0, 0, c, d+2*k, 0)
theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 2)); ring_nf; finish

-- Main transition: canonical state D to canonical state 2*D+2
-- (0, 0, D+2, D, 0) ⊢⁺ (0, 0, 2*D+4, 2*D+2, 0)
theorem main_trans (D : ℕ) :
    ⟨0, 0, D + 2, D, 0⟩ [fm]⊢⁺
    ⟨0, 0, 2 * D + 4, 2 * D + 2, 0⟩ := by
  -- Phase 1: R5 step
  -- (0, 0, D+2, D, 0) -> (1, 0, D+1, D+1, 0)
  have h1 : ⟨0, 0, D + 2, D, 0⟩ [fm]⊢⁺
      ⟨1, 0, D + 1, D + 1, 0⟩ := by
    rw [show D + 2 = (D + 1) + 1 from by ring]
    apply step_stepPlus
    show fm ⟨0, 0, (D + 1) + 1, D, 0⟩ = some ⟨1, 0, D + 1, D + 1, 0⟩
    unfold fm; simp only
  -- Phase 2: R2/R1 chain
  -- (1, 0, D+1, D+1, 0) ⊢* (D+2, 0, 0, 0, D+1)
  have h2 : ⟨1, 0, D + 1, D + 1, 0⟩ [fm]⊢*
      ⟨D + 2, 0, 0, 0, D + 1⟩ := by
    have := r2r1_chain (D + 1) 0 0
    rw [show 0 + (D + 1) + 1 = D + 2 from by ring,
        show 0 + (D + 1) = D + 1 from by ring] at this
    ring_nf at this ⊢; exact this
  -- Phase 3: R3 drain
  -- (D+2, 0, 0, 0, D+1) ⊢* (0, 0, 2*(D+2), 0, D+1)
  have h3 : ⟨D + 2, 0, 0, 0, D + 1⟩ [fm]⊢*
      ⟨0, 0, 2 * D + 4, 0, D + 1⟩ := by
    have := r3_drain (D + 2) 0 (D + 1)
    rw [show 0 + 2 * (D + 2) = 2 * D + 4 from by ring] at this
    exact this
  -- Phase 4: R4 drain
  -- (0, 0, 2*D+4, 0, D+1) ⊢* (0, 0, 2*D+4, 2*D+2, 0)
  have h4 : ⟨0, 0, 2 * D + 4, 0, D + 1⟩ [fm]⊢*
      ⟨0, 0, 2 * D + 4, 2 * D + 2, 0⟩ := by
    have := r4_drain (D + 1) (2 * D + 4) 0
    rw [show 0 + 2 * (D + 1) = 2 * D + 2 from by ring] at this
    exact this
  -- Compose all phases
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun D ↦ ⟨0, 0, D + 2, D, 0⟩) 0
  intro D
  refine ⟨2 * D + 2, ?_⟩
  show ⟨0, 0, D + 2, D, 0⟩ [fm]⊢⁺
    ⟨0, 0, (2 * D + 2) + 2, 2 * D + 2, 0⟩
  rw [show (2 * D + 2) + 2 = 2 * D + 4 from by ring]
  exact main_trans D
