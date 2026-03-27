import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #600: [35/6, 121/2, 4/55, 3/7, 18/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 1  2  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6

---

Canonical states: (0, 0, 0, 2n, n^2 + 2n + 2) for n >= 1.

Phases per transition:
1. R4 chain: d -> b
2. R5: one step
3. R1/R3/R1 interleaved: 3-step rounds consuming b
4. R2: one step
5. R3/R2/R2 drain: consuming c
-/

namespace Sz22_2003_unofficial_600

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | _ => none

-- Phase 1: R4 chain, convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b+k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  rw [show b + (k + 1) = (b + 1) + k from by omega]
  step fm
  exact ih _

-- Phase 3: R1/R3/R1 interleaved rounds
-- Each round: (1, B+2, C, D, E+1) -> (1, B, C+1, D+2, E)
theorem interleave : ∀ k c d e, ⟨1, 2*k, c, d, e+k⟩ [fm]⊢* ⟨1, 0, c+k, d+2*k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 5: R3/R2/R2 drain, consuming c
-- Each round: (0, 0, c+1, d, e+1) -> (0, 0, c, d, e+4)
theorem drain_c : ∀ k e, ⟨0, 0, k, d, e+1⟩ [fm]⊢* ⟨0, 0, 0, d, e+1+3*k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  step fm; step fm; step fm
  apply stepStar_trans (ih _)
  ring_nf; finish

-- Main transition: C(n) ⊢⁺ C(n+1) where C(n) = (0, 0, 0, 2*n, n^2+2*n+2)
theorem main_trans (n : ℕ) :
    (⟨0, 0, 0, 2*n, n^2+2*n+2⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, 2*(n+1), (n+1)^2+2*(n+1)+2⟩ := by
  -- Phase 1: d_to_b (⊢*)
  apply stepStar_stepPlus_stepPlus (d_to_b (2*n) 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5 (⊢⁺, the step that makes progress)
  rw [show n ^ 2 + 2 * n + 2 = n ^ 2 + 2 * n + 1 + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; simp only; rfl)
  simp only [Nat.reduceAdd]
  -- Phase 3: interleave (⊢*)
  rw [show 2 * n + 2 = 2 * (n + 1) from by ring,
      show n ^ 2 + 2 * n + 1 = n ^ 2 + n + (n + 1) from by ring]
  apply stepStar_trans (interleave (n+1) 0 0 (n^2+n))
  simp only [Nat.zero_add]
  -- Phase 4: R2 (⊢*)
  step fm
  -- Phase 5: drain_c (⊢*)
  rw [show n ^ 2 + n + 2 = (n ^ 2 + n + 1) + 1 from by ring]
  apply stepStar_trans (drain_c (n+1) (n^2+n+1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 5⟩) (by execute fm 9)
  have : (⟨0, 0, 0, 2, 5⟩ : Q) = ⟨0, 0, 0, 2*1, 1^2+2*1+2⟩ := by ring_nf
  rw [this]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2*(n+1), (n+1)^2+2*(n+1)+2⟩) 0
  intro n; exists n + 1; exact main_trans (n + 1)

end Sz22_2003_unofficial_600
