import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #920: [4/15, 33/14, 125/2, 7/11, 33/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  3  0  0
 0  0  0  1 -1
 0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_920

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- Phase: R1/R2 interleaved chain
-- From (a, 1, c+d+1, d, e) to (a+d, 1, c+1, 0, e+d)
theorem r1r2_chain : ∀ d, ∀ a c e,
    ⟨a, 1, c + d + 1, d, e⟩ [fm]⊢* ⟨a + d, 1, c + 1, 0, e + d⟩ := by
  intro d; induction' d with d ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + (d + 1) + 1 = (c + d + 1) + 1 from by ring,
        show (d : ℕ) + 1 = d + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

-- Phase: R3 drain — a fires of R3
-- From (k, 0, c, 0, e) to (0, 0, c+3*k, 0, e)
theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 3) e); ring_nf; finish

-- Phase: R4 drain — e fires of R4
-- From (0, 0, c, d, k) to (0, 0, c, d+k, 0)
theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

-- Main transition: canonical state n to canonical state n+1
-- (0, 0, n^2+3n+3, n, 0) ⊢⁺ (0, 0, (n+1)^2+3(n+1)+3, n+1, 0)
-- i.e. (0, 0, n^2+3n+3, n, 0) ⊢⁺ (0, 0, n^2+5n+7, n+1, 0)
theorem main_trans (n : ℕ) :
    ⟨0, 0, n * n + 3 * n + 3, n, 0⟩ [fm]⊢⁺
    ⟨0, 0, n * n + 5 * n + 7, n + 1, 0⟩ := by
  -- Phase 1: R5 step
  -- (0, 0, n^2+3n+3, n, 0) -> (0, 1, n^2+3n+2, n, 1)
  have h1 : ⟨0, 0, n * n + 3 * n + 3, n, 0⟩ [fm]⊢⁺
      ⟨0, 1, n * n + 3 * n + 2, n, 1⟩ := by
    rw [show n * n + 3 * n + 3 = (n * n + 3 * n + 2) + 1 from by ring]
    apply step_stepPlus
    show fm ⟨0, 0, (n * n + 3 * n + 2) + 1, n, 0⟩ = some ⟨0, 1, n * n + 3 * n + 2, n, 1⟩
    unfold fm; simp only
  -- Phase 2: R1/R2 chain
  -- (0, 1, n^2+3n+2, n, 1) ⊢* (n, 1, n^2+2n+2, 0, n+1)
  have h2 : ⟨0, 1, n * n + 3 * n + 2, n, 1⟩ [fm]⊢*
      ⟨n, 1, n * n + 2 * n + 2, 0, n + 1⟩ := by
    have := r1r2_chain n 0 (n * n + 2 * n + 1) 1
    rw [show (n * n + 2 * n + 1) + n + 1 = n * n + 3 * n + 2 from by ring,
        show (n * n + 2 * n + 1) + 1 = n * n + 2 * n + 2 from by ring] at this
    ring_nf at this ⊢; exact this
  -- Phase 3: Final R1 step
  -- (n, 1, n^2+2n+2, 0, n+1) -> (n+2, 0, n^2+2n+1, 0, n+1)
  have h3 : ⟨n, 1, n * n + 2 * n + 2, 0, n + 1⟩ [fm]⊢*
      ⟨n + 2, 0, n * n + 2 * n + 1, 0, n + 1⟩ := by
    rw [show n * n + 2 * n + 2 = (n * n + 2 * n + 1) + 1 from by ring]
    apply step_stepStar
    show fm ⟨n, 1, (n * n + 2 * n + 1) + 1, 0, n + 1⟩ = some ⟨n + 2, 0, n * n + 2 * n + 1, 0, n + 1⟩
    unfold fm; simp only
  -- Phase 4: R3 drain
  -- (n+2, 0, (n+1)^2, 0, n+1) ⊢* (0, 0, (n+1)^2 + 3*(n+2), 0, n+1)
  have h4 : ⟨n + 2, 0, n * n + 2 * n + 1, 0, n + 1⟩ [fm]⊢*
      ⟨0, 0, n * n + 5 * n + 7, 0, n + 1⟩ := by
    have := r3_drain (n + 2) (n * n + 2 * n + 1) (n + 1)
    rw [show (n * n + 2 * n + 1) + 3 * (n + 2) = n * n + 5 * n + 7 from by ring] at this
    exact this
  -- Phase 5: R4 drain
  -- (0, 0, n^2+5n+7, 0, n+1) ⊢* (0, 0, n^2+5n+7, n+1, 0)
  have h5 : ⟨0, 0, n * n + 5 * n + 7, 0, n + 1⟩ [fm]⊢*
      ⟨0, 0, n * n + 5 * n + 7, n + 1, 0⟩ := by
    have := r4_drain (n + 1) (n * n + 5 * n + 7) 0
    rw [show 0 + (n + 1) = n + 1 from by ring] at this
    exact this
  -- Compose all phases
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n * n + 3 * n + 3, n, 0⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨0, 0, n * n + 3 * n + 3, n, 0⟩ [fm]⊢⁺
    ⟨0, 0, (n + 1) * (n + 1) + 3 * (n + 1) + 3, n + 1, 0⟩
  rw [show (n + 1) * (n + 1) + 3 * (n + 1) + 3 = n * n + 5 * n + 7 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_920
