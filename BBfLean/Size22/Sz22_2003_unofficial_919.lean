import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #919: [4/15, 33/14, 125/2, 7/11, 22/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  3  0  0
 0  0  0  1 -1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_919

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- Phase 1: R3 drain a. (a+k, 0, c, 0, e) ⊢* (a, 0, c+3*k, 0, e)
theorem r3_drain : ∀ k, ∀ a c e,
    ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a (c + 3) e); ring_nf; finish

-- Phase 2: e-to-d transfer. (0, 0, c, d, e+k) ⊢* (0, 0, c, d+k, e)
theorem e_to_d : ∀ k, ∀ c d e,
    ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih c (d + 1) e); ring_nf; finish

-- Phase 3: R2+R1 chain with general e.
-- Each round: R2 then R1.
-- R2: (a+1, 0, c, d+1, e) -> (a, 1, c, d, e+1)
-- R1: (a, 1, c+1, d, e) -> (a+2, 0, c, d, e)  [but after R2 we have b=1, c same]
-- Combined R2+R1: (a+1, 0, c+1, d+1, e) -> (a+2, 0, c, d, e+1)
-- Net: a+=1, c-=1, d-=1, e+=1
-- k rounds: (a+1, 0, c+k, d+k, e) ⊢* (a+k+1, 0, c, d, e+k)
theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1)); ring_nf; finish

-- Full interleaved phase: R5 then R2+R1 chain
-- From (0, 0, C+n+1, n+1, 0):
--   R5: (1, 0, C+n, n+1, 1)
--   r2r1_chain (n+1): (1, 0, C+n+1-1, n+1, 1) but we need (0+1, 0, C+(n+1), 0+(n+1), 1)
--   Result: (0+(n+1)+1, 0, C, 0, 1+(n+1)) = (n+2, 0, C, 0, n+2)
theorem r5_r2r1 (C n : ℕ) :
    ⟨0, 0, C + n + 2, n + 1, 0⟩ [fm]⊢⁺ ⟨n + 2, 0, C, 0, n + 2⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, C + n + 2, n + 1, 0⟩ = some ⟨1, 0, C + n + 1, n + 1, 1⟩
    unfold fm; simp only
  have h := r2r1_chain (n + 1) 0 C 0 1
  ring_nf at h ⊢; exact h

-- Main transition: (n+4, 0, n^2+6n+11, 0, n+4) ⊢⁺ (n+5, 0, n^2+8n+18, 0, n+5)
-- Phase 1: R3 drain (n+4 times):
--   (n+4, 0, n^2+6n+11, 0, n+4) ⊢* (0, 0, n^2+6n+11+3*(n+4), 0, n+4)
--   = (0, 0, n^2+9n+23, 0, n+4)
-- Phase 2: e-to-d (n+4 times):
--   (0, 0, n^2+9n+23, 0, n+4) ⊢* (0, 0, n^2+9n+23, n+4, 0)
-- Phase 3: R5+R2R1 chain:
--   (0, 0, n^2+9n+23, n+4, 0)
--   We need C + (n+3) + 2 = n^2+9n+23 and the d = (n+3)+1 = n+4
--   So C = n^2+9n+23 - n - 5 = n^2+8n+18
--   Result: (n+5, 0, n^2+8n+18, 0, n+5)
-- This matches (n+1) param: ((n+1)+4, 0, (n+1)^2+6(n+1)+11, 0, (n+1)+4) = (n+5, 0, n^2+8n+18, 0, n+5) ✓

theorem main_trans (n : ℕ) :
    ⟨n + 4, 0, n * n + 6 * n + 11, 0, n + 4⟩ [fm]⊢⁺
    ⟨n + 5, 0, n * n + 8 * n + 18, 0, n + 5⟩ := by
  -- Phase 1: R3 drain
  have h1 : ⟨n + 4, 0, n * n + 6 * n + 11, 0, n + 4⟩ [fm]⊢*
      ⟨0, 0, n * n + 9 * n + 23, 0, n + 4⟩ := by
    have := r3_drain (n + 4) 0 (n * n + 6 * n + 11) (n + 4)
    ring_nf at this ⊢; exact this
  -- Phase 2: e-to-d transfer
  have h2 : ⟨0, 0, n * n + 9 * n + 23, 0, n + 4⟩ [fm]⊢*
      ⟨0, 0, n * n + 9 * n + 23, n + 4, 0⟩ := by
    have := e_to_d (n + 4) (n * n + 9 * n + 23) 0 0
    ring_nf at this ⊢; exact this
  -- Phase 3: R5+R2R1
  have h3 : ⟨0, 0, n * n + 9 * n + 23, n + 4, 0⟩ [fm]⊢⁺
      ⟨n + 5, 0, n * n + 8 * n + 18, 0, n + 5⟩ := by
    have := r5_r2r1 (n * n + 8 * n + 18) (n + 3)
    ring_nf at this ⊢; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2 h3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 11, 0, 4⟩)
  · execute fm 29
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 4, 0, n * n + 6 * n + 11, 0, n + 4⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨n + 4, 0, n * n + 6 * n + 11, 0, n + 4⟩ [fm]⊢⁺
    ⟨(n + 1) + 4, 0, (n + 1) * (n + 1) + 6 * (n + 1) + 11, 0, (n + 1) + 4⟩
  rw [show (n + 1) + 4 = n + 5 from by ring,
      show (n + 1) * (n + 1) + 6 * (n + 1) + 11 = n * n + 8 * n + 18 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_919
