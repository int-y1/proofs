import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #930: [4/15, 33/14, 25/2, 7/11, 21/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_930

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Phase: R3 drain (consumes a, adds 2 to c per step)
theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) e); ring_nf; finish

-- Phase: R4 drain (transfers e to d)
theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

-- Phase: R2/R1 interleaved chain
-- From (a, 0, c+d, d, e) after d rounds of (R2, R1): (a+d, 0, c, 0, e+d)
-- Each round needs a>=1 and d>=1 for R2, and b=1 and c>=1 for R1.
theorem r2r1_chain : ∀ d, ∀ a c e,
    ⟨a + 1, 0, c + d, d, e⟩ [fm]⊢* ⟨a + d + 1, 0, c, 0, e + d⟩ := by
  intro d; induction' d with d ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + (d + 1) = (c + d) + 1 from by ring,
        show (d : ℕ) + 1 = d + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

-- Main transition: (n+2, 0, c, 0, n) ⊢⁺ (n+3, 0, c+n+1, 0, n+1)
-- Phases:
--   1. R3 drain: (n+2, 0, c, 0, n) ⊢* (0, 0, c+2n+4, 0, n)
--   2. R4 drain: (0, 0, c+2n+4, 0, n) ⊢* (0, 0, c+2n+4, n, 0)
--   3. R5: (0, 0, c+2n+4, n, 0) → (0, 1, c+2n+3, n+1, 0)
--   4. R1: (0, 1, c+2n+3, n+1, 0) → (2, 0, c+2n+2, n+1, 0)
--   5. R2/R1 chain (n+1 rounds): (2, 0, c+2n+2, n+1, 0) ⊢* (n+3, 0, c+n+1, 0, n+1)
theorem main_trans (c n : ℕ) :
    ⟨n + 2, 0, c, 0, n⟩ [fm]⊢⁺ ⟨n + 3, 0, c + n + 1, 0, n + 1⟩ := by
  -- Phase 1: R3 drain
  have h1 : ⟨n + 2, 0, c, 0, n⟩ [fm]⊢⁺
      ⟨0, 0, c + 2 * (n + 2), 0, n⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]
    apply step_stepStar_stepPlus
    · show fm ⟨(n + 1) + 1, 0, c, 0, n⟩ = some ⟨n + 1, 0, c + 2, 0, n⟩
      unfold fm; simp only
    · have := r3_drain (n + 1) (c + 2) n
      rw [show c + 2 + 2 * (n + 1) = c + 2 * (n + 2) from by ring] at this
      exact this
  -- Phase 2: R4 drain
  have h2 : ⟨0, 0, c + 2 * (n + 2), 0, n⟩ [fm]⊢*
      ⟨0, 0, c + 2 * (n + 2), n, 0⟩ := by
    have := r4_drain n (c + 2 * (n + 2)) 0
    rw [show 0 + n = n from by ring] at this
    exact this
  -- Phase 3: R5
  have h3 : ⟨0, 0, c + 2 * (n + 2), n, 0⟩ [fm]⊢*
      ⟨0, 1, c + (2 * n + 3), n + 1, 0⟩ := by
    rw [show c + 2 * (n + 2) = (c + (2 * n + 3)) + 1 from by ring]
    apply step_stepStar
    show fm ⟨0, 0, (c + (2 * n + 3)) + 1, n, 0⟩ = some ⟨0, 1, c + (2 * n + 3), n + 1, 0⟩
    unfold fm; simp only
  -- Phase 4: R1
  have h4 : ⟨0, 1, c + (2 * n + 3), n + 1, 0⟩ [fm]⊢*
      ⟨2, 0, c + (2 * n + 2), n + 1, 0⟩ := by
    rw [show c + (2 * n + 3) = (c + (2 * n + 2)) + 1 from by ring]
    apply step_stepStar
    show fm ⟨0, 1, (c + (2 * n + 2)) + 1, n + 1, 0⟩ = some ⟨2, 0, c + (2 * n + 2), n + 1, 0⟩
    unfold fm; simp only
  -- Phase 5: R2/R1 chain (n+1 rounds)
  have h5 : ⟨2, 0, c + (2 * n + 2), n + 1, 0⟩ [fm]⊢*
      ⟨n + 3, 0, c + n + 1, 0, n + 1⟩ := by
    have := r2r1_chain (n + 1) 1 (c + n + 1) 0
    rw [show 1 + 1 = 2 from by ring,
        show (c + n + 1) + (n + 1) = c + (2 * n + 2) from by ring,
        show 1 + (n + 1) + 1 = n + 3 from by ring,
        show 0 + (n + 1) = n + 1 from by ring] at this
    exact this
  -- Compose all phases
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 4, 0, 3⟩) (by execute fm 29)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, n⟩ ↦ ⟨n + 2, 0, c, 0, n⟩) ⟨4, 3⟩
  intro ⟨c, n⟩
  exact ⟨⟨c + n + 1, n + 1⟩, main_trans c n⟩

end Sz22_2003_unofficial_930
