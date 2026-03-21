import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #140: [9/35, 65/33, 14/3, 11/13, 39/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  1  0  0
 0  0  0  0  1 -1
-1  1  0  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_140

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | _ => none

-- Phase 1 chain: (R2, R1) pairs
-- From ⟨a, j+1, 0, k, k, j+1⟩, apply R2 then R1, decreasing k and increasing j.
-- After k rounds: ⟨a, j+k+1, 0, 0, 0, j+k+1⟩
theorem r2r1_rounds : ⟨a, j+1, 0, k, k, j+1⟩ [fm]⊢* ⟨a, j+k+1, 0, 0, 0, j+k+1⟩ := by
  have many_step : ∀ k j, ⟨a, j+1, 0, k, k, j+1⟩ [fm]⊢* ⟨a, j+k+1, 0, 0, 0, j+k+1⟩ := by
    intro k; induction' k with k ih <;> intro j
    · exists 0
    show ⟨a, j+1, 0, k+1, k+1, j+1⟩ [fm]⊢* ⟨a, j+(k+1)+1, 0, 0, 0, j+(k+1)+1⟩
    -- R2: b=j+1≥1, e=k+1≥1 → ⟨a, j, 1, k+1, k, j+2⟩
    step fm
    -- R1: c=1, d=k+1≥1 → ⟨a, j+2, 0, k, k, j+2⟩
    step fm
    apply stepStar_trans (ih (j+1))
    ring_nf; finish
  exact many_step k j

-- Phase 2: R3 repeated (b → a, d) when e=0
-- Each step: ⟨a, b+1, 0, d, 0, f⟩ → ⟨a+1, b, 0, d+1, 0, f⟩
theorem b_to_ad : ⟨a, b+k, 0, d, 0, f⟩ [fm]⊢* ⟨a+k, b, 0, d+k, 0, f⟩ := by
  have many_step : ∀ k a d, ⟨a, b+k, 0, d, 0, f⟩ [fm]⊢* ⟨a+k, b, 0, d+k, 0, f⟩ := by
    intro k; induction' k with k ih <;> intro a d
    · exists 0
    rw [show b + (k+1) = (b+k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact many_step k a d

-- Phase 3: R4 repeated (f → e) when a=0, b=0, c=0
-- Each step: ⟨a, 0, 0, d, e, f+1⟩ → ⟨a, 0, 0, d, e+1, f⟩
theorem f_to_e : ⟨a, 0, 0, d, e, f+k⟩ [fm]⊢* ⟨a, 0, 0, d, e+k, f⟩ := by
  have many_step : ∀ k e, ⟨a, 0, 0, d, e, f+k⟩ [fm]⊢* ⟨a, 0, 0, d, e+k, f⟩ := by
    intro k; induction' k with k ih <;> intro e
    · exists 0
    rw [show f + (k+1) = (f+k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish
  exact many_step k e

-- Main transition: (a+1, 0, 0, n, n, 0) →⁺ (a+n+1, 0, 0, n+1, n+1, 0)
-- Phase 1: R5 gives (a, 1, 0, n, n, 1)
-- Phase 1 chain: r2r1_rounds gives (a, n+1, 0, 0, 0, n+1)
-- Phase 2: b_to_ad gives (a+n+1, 0, 0, n+1, 0, n+1)
-- Phase 3: f_to_e gives (a+n+1, 0, 0, n+1, n+1, 0)
theorem main_trans : ⟨a+1, 0, 0, n, n, 0⟩ [fm]⊢⁺ ⟨a+n+1, 0, 0, n+1, n+1, 0⟩ := by
  -- Phase 1: R5: (a+1, 0, 0, n, n, 0) → (a, 1, 0, n, n, 1)
  step fm
  -- Phase 1 chain: r2r1_rounds with j=0
  apply stepStar_trans (c₂ := ⟨a, n+1, 0, 0, 0, n+1⟩)
  · have h := @r2r1_rounds a 0 n
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 2: b_to_ad with b=0, k=n+1
  apply stepStar_trans (c₂ := ⟨a+(n+1), 0, 0, n+1, 0, n+1⟩)
  · have h := @b_to_ad a 0 (n+1) 0 (n+1)
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 3: f_to_e with f=0, k=n+1
  have h := @f_to_e (a+(n+1)) (n+1) 0 0 (n+1)
  simp only [Nat.zero_add] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 2, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a+1, 0, 0, n, n, 0⟩) ⟨1, 2⟩
  intro ⟨a, n⟩
  exists ⟨a+n, n+1⟩
  -- goal: (a+1, 0, 0, n, n, 0) ⊢⁺ (a+n+1, 0, 0, n+1, n+1, 0)
  -- C(a+n, n+1) = ((a+n)+1, 0, 0, n+1, n+1, 0)
  exact main_trans
