import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #316: [154/15, 21/2, 1/3, 25/7, 1/55, 3/5]

Vector representation:
```
 1 -1 -1  1  1
-1  1  0  1  0
 0 -1  0  0  0
 0  0  2 -1  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_316

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1: Rule 4 drains d into c: (0, 0, c, d+k, e) →* (0, 0, c+2k, d, e)
theorem phase1 (d : ℕ) : ∀ k c e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + 2*k, d, e⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Phase 2: Rule 5 drains e from c: (0, 0, c+k, 0, k) →* (0, 0, c, 0, 0)
theorem phase2 : ∀ k c, ⟨0, 0, c + k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro c; exists 0
  | succ k ih =>
    intro c
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    exact ih _

-- Rules 1+2 chain k times: (0, 1, c+1+k, d, e) →* (0, 1, c+1, d+2*k, e+k)
-- Requires c+1+k >= 1, which is always true.
theorem r12_chain : ∀ k c d e, ⟨0, 1, c + 1 + k, d, e⟩ [fm]⊢* ⟨0, 1, c + 1, d + 2*k, e + k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + 1 + (k + 1) = (c + 1 + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Main cycle: (0, 0, 0, 2*(n+1), n+1) →⁺ (0, 0, 0, 6*n+4, 3*n+2)
theorem cycle (n : ℕ) : ⟨0, 0, 0, 2*(n+1), n+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 6*n+4, 3*n+2⟩ := by
  -- Phase 1: drain d into c
  rw [show 2*(n+1) = 0 + (2*(n+1)) from by ring]
  apply stepStar_stepPlus_stepPlus
    (phase1 0 (2*(n+1)) 0 (n+1))
  simp only [Nat.zero_add]
  -- Now at (0, 0, 2*(2*(n+1)), 0, n+1) = (0, 0, (3*n+3)+(n+1), 0, n+1)
  -- Phase 2: drain e from c
  rw [show 2 * (2 * (n + 1)) = (3*n+3) + (n+1) from by ring]
  apply stepStar_stepPlus_stepPlus (phase2 (n+1) (3*n+3))
  -- Now at (0, 0, 3*n+3, 0, 0) = (0, 0, (3*n+2)+1, 0, 0)
  -- Phase 3: rule 6 once
  rw [show 3*n+3 = (3*n+2) + 1 from by ring]
  step fm
  -- Now at (0, 1, 3*n+2, 0, 0) = (0, 1, (0+1)+(3*n+1), 0, 0)
  -- Phase 4: rules 1+2 chain (3*n+1 times), then rule 3
  rw [show 3*n+2 = 0 + 1 + (3*n+1) from by ring]
  apply stepStar_trans (r12_chain (3*n+1) 0 0 0)
  -- Now at (0, 1, 0+1, 2*(3*n+1), 3*n+1) = (0, 1, 1, 6*n+2, 3*n+1)
  -- Rule 1: (1, 0, 0, 6*n+3, 3*n+2)
  step fm
  -- Rule 2: (0, 1, 0, 6*n+4, 3*n+2)
  step fm
  -- Rule 3: (0, 0, 0, 6*n+4, 3*n+2)
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 7
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, 0, 2*(n+1), n+1⟩)
  · intro c ⟨n, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, 6*n+4, 3*n+2⟩,
           ⟨3*n+1, by ring_nf⟩,
           cycle n⟩
  · exact ⟨0, rfl⟩
