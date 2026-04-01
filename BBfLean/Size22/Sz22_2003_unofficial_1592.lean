import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1592: [72/35, 5/3, 1/10, 49/2, 6/7]

Vector representation:
```
 3  2 -1 -1
 0 -1  1  0
-1  0 -1  0
-1  0  0  2
 1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1592

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+3, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a+1, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b+1, c, d⟩
  | _ => none

-- R2-R1 chain: k pairs of (R2, R1). Each pair: a += 3, b_net += 1, d -= 1.
theorem r2r1_chain : ∀ k, ∀ a b d, ⟨a, b + 1, 0, d + k⟩ [fm]⊢* ⟨a + 3 * k, b + k + 1, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring]
    step fm  -- R2: (a, b, 1, d+k+1)
    step fm  -- R1: (a+3, b+2, 0, d+k)
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (b + 1) d)
    ring_nf; finish

-- Phase 1: spiral (0, 0, 0, d+2) ->* (3d+4, d+2, 0, 0)
theorem phase1 : ∀ d, ⟨0, 0, 0, d + 2⟩ [fm]⊢* ⟨3 * d + 4, d + 2, 0, 0⟩ := by
  intro d
  rw [show d + 2 = d + 1 + 1 from by ring]
  step fm  -- R5: (1, 1, 0, d+1)
  rw [show d + 1 = d + 0 + 1 from by ring]
  step fm  -- R2: (1, 0, 1, d+0+1)
  step fm  -- R1: (4, 2, 0, d+0)
  rw [show (2 : ℕ) = 1 + 1 from by ring, show d = 0 + d from by ring]
  apply stepStar_trans (r2r1_chain d 4 1 0)
  ring_nf; finish

-- Phase 2: R2 drains b to c.
theorem b_to_c : ∀ k, ∀ a b c, ⟨a, b + k, c, 0⟩ [fm]⊢* ⟨a, b, c + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (c + 1))
    ring_nf; finish

-- Phase 3: R3 drains c using a.
theorem c_drain : ∀ k, ∀ a, ⟨a + k, 0, k, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    exact ih a

-- Phase 4: R4 drains a to d.
theorem a_to_d : ∀ k, ∀ a d, ⟨a + k, 0, 0, d⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2))
    ring_nf; finish

-- Full transition: (0, 0, 0, d+2) ->+ (0, 0, 0, 4d+4)
theorem main_trans : ∀ d, ⟨0, 0, 0, d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * d + 4⟩ := by
  intro d
  -- Phase 1: (0, 0, 0, d+2) ->* (3d+4, d+2, 0, 0)
  apply stepStar_stepPlus_stepPlus (phase1 d)
  -- Need: (3d+4, d+2, 0, 0) ->+ (0, 0, 0, 4d+4)
  -- Phase 2: (3d+4, d+2, 0, 0) ->* (3d+4, 0, d+2, 0)
  apply stepStar_stepPlus_stepPlus
  · rw [show (d + 2 : ℕ) = 0 + (d + 2) from by ring]
    exact b_to_c (d + 2) (3 * d + 4) 0 0
  -- Phase 3: (3d+4, 0, d+2, 0) ->* (2d+2, 0, 0, 0)
  apply stepStar_stepPlus_stepPlus
  · rw [show 3 * d + 4 = (2 * d + 2) + (d + 2) from by ring,
        show 0 + (d + 2) = d + 2 from by ring]
    exact c_drain (d + 2) (2 * d + 2)
  -- Phase 4: (2d+2, 0, 0, 0) ->+ (0, 0, 0, 4d+4)
  -- First R4 step: (2d+2, 0, 0, 0) -> (2d+1, 0, 0, 2)
  rw [show 2 * d + 2 = (2 * d + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨2 * d + 1, 0, 0, 2⟩) (by simp [fm])
  -- Now: (2d+1, 0, 0, 2) ->* (0, 0, 0, 4d+4)
  rw [show 2 * d + 1 = 0 + (2 * d + 1) from by ring]
  apply stepStar_trans (a_to_d (2 * d + 1) 0 2)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d + 2⟩) 0
  intro d; exists (4 * d + 2)
  exact main_trans d

end Sz22_2003_unofficial_1592
