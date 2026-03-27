import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #409: [25/63, 1/55, 12/5, 847/2, 3/11]

Vector representation:
```
 0 -2  2 -1  0
 0  0 -1  0 -1
 2  1 -1  0  0
-1  0  0  1  2
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_409

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Rule 4 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d+k, e+2k)
theorem r4_chain : ∀ k a d e,
    ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+k, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a (d + 1) (e + 2))
  ring_nf; finish

-- d-reduction: one step. (0, 0, 0, d+1, e+4) →* (0, 0, 0, d, e)
theorem d_reduce_one : ∀ d e,
    ⟨0, 0, 0, d+1, e+4⟩ [fm]⊢* ⟨0, 0, 0, d, e⟩ := by
  intro d e
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- d-reduction iterated k times: (0, 0, 0, d+k, e+4k) →* (0, 0, 0, d, e)
theorem d_reduce_iter : ∀ k d e,
    ⟨0, 0, 0, d+k, e+4*k⟩ [fm]⊢* ⟨0, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show e + 4 * (k + 1) = (e + 4 * k) + 4 from by ring]
  apply stepStar_trans (d_reduce_one _ _)
  exact ih d e

-- Tail: (0, 0, 0, m+1, 2) →* (0, 0, 2, m, 0)
theorem tail_phase : ∀ m,
    ⟨0, 0, 0, m+1, 2⟩ [fm]⊢* ⟨0, 0, 2, m, 0⟩ := by
  intro m
  step fm; step fm; step fm; finish

-- a-growth one step: (a, 0, 2, d+1, 0) →* (a+4, 0, 2, d, 0)
theorem a_grow_one : ∀ a d,
    ⟨a, 0, 2, d+1, 0⟩ [fm]⊢* ⟨a+4, 0, 2, d, 0⟩ := by
  intro a d
  step fm; step fm; step fm
  ring_nf; finish

-- a-growth iterated: (a, 0, 2, d+k, 0) →* (a+4k, 0, 2, d, 0)
theorem a_grow_iter : ∀ k a d,
    ⟨a, 0, 2, d+k, 0⟩ [fm]⊢* ⟨a+4*k, 0, 2, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  apply stepStar_trans (a_grow_one _ _)
  apply stepStar_trans (ih (a + 4) d)
  ring_nf; finish

-- a-growth final: (a, 0, 2, 0, 0) →* (a+4, 2, 0, 0, 0)
theorem a_grow_final : ∀ a,
    ⟨a, 0, 2, 0, 0⟩ [fm]⊢* ⟨a+4, 2, 0, 0, 0⟩ := by
  intro a
  step fm; step fm
  ring_nf; finish

-- Cleanup: (a+1, 2, 0, 0, 0) →* (a, 0, 0, 0, 0)
theorem cleanup : ∀ a,
    ⟨a+1, 2, 0, 0, 0⟩ [fm]⊢* ⟨a, 0, 0, 0, 0⟩ := by
  intro a
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Full phase 2-5: (0, 0, 0, m+1+m, 2+4*m) →* (4*m+3, 0, 0, 0, 0)
theorem phases_2_to_5 (m : ℕ) :
    ⟨0, 0, 0, m+1+m, 2+4*m⟩ [fm]⊢* ⟨4*m+3, 0, 0, 0, 0⟩ := by
  apply stepStar_trans (d_reduce_iter m (m+1) 2)
  apply stepStar_trans (tail_phase m)
  apply stepStar_trans
  · have h := a_grow_iter m 0 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (a_grow_final (4 * m))
  have h := cleanup (4 * m + 3)
  rw [show 4 * m + 3 + 1 = 4 * m + 4 from by ring] at h
  exact h

-- Main transition: (2*m+1, 0, 0, 0, 0) →⁺ (4*m+3, 0, 0, 0, 0)
theorem main_trans (m : ℕ) :
    ⟨2*m+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨4*m+3, 0, 0, 0, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨2*m+1, 0, 0, 0, 0⟩ = some ⟨2*m, 0, 0, 1, 2⟩; rfl
  apply stepStar_trans
  · have h := r4_chain (2*m) 0 1 2
    simp only [Nat.zero_add] at h; exact h
  -- Now at (0, 0, 0, 1+2*m, 2+2*(2*m))
  -- Need to show this equals (0, 0, 0, m+1+m, 2+4*m)
  show ⟨0, 0, 0, 1+2*m, 2+2*(2*m)⟩ [fm]⊢* ⟨4*m+3, 0, 0, 0, 0⟩
  rw [show 1 + 2 * m = m + 1 + m from by ring,
      show 2 + 2 * (2 * m) = 2 + 4 * m from by ring]
  exact phases_2_to_5 m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨2*m+1, 0, 0, 0, 0⟩) 0
  intro m
  refine ⟨2*m+1, ?_⟩
  show ⟨2*m+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨2*(2*m+1)+1, 0, 0, 0, 0⟩
  rw [show 2 * (2 * m + 1) + 1 = 4 * m + 3 from by ring]
  exact main_trans m

end Sz22_2003_unofficial_409
