import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #40: [1/15, 44/21, 3/22, 245/2, 33/5]

Vector representation:
```
 0 -1 -1  0  0
 2 -1  0 -1  1
-1  1  0  0 -1
-1  0  1  2  0
 0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_40

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+2, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R1/R5 interleave: (0, 1, 2*k, d, e) ->* (0, 1, 0, d, e+k)
theorem r1r5_chain : ∀ k, ∀ d e, ⟨0, 1, 2*k, d, e⟩ [fm]⊢* ⟨0, 1, 0, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase A: (0, 0, 2*k+1, d, e) ->* (0, 1, 0, d, e+k+1)
theorem phase_A : ∀ k, ∀ d e, ⟨0, 0, 2*k+1, d, e⟩ [fm]⊢* ⟨0, 1, 0, d, e+k+1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · step fm; finish
  rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3/R2 interleave: (a+1, 0, 0, d+j, e+1) ->* (a+j+1, 0, 0, d, e+1)
theorem r3r2_chain : ∀ j, ∀ a d, ⟨a+1, 0, 0, d+j, e+1⟩ [fm]⊢* ⟨a+j+1, 0, 0, d, e+1⟩ := by
  intro j; induction' j with j ih <;> intro a d
  · exists 0
  rw [show d + (j + 1) = (d + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3 drain: (a+k, b, 0, 0, k) ->* (a, b+k, 0, 0, 0)
theorem r3_drain : ∀ k, ∀ a b, ⟨a+k, b, 0, 0, k⟩ [fm]⊢* ⟨a, b+k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase E inner: (a+1, b+3, 0, 0, 0) ->* (a+2, b+2, 0, 0, 0)
theorem phase_E_inner : ⟨a+1, b+3, 0, 0, 0⟩ [fm]⊢* ⟨a+2, b+2, 0, 0, 0⟩ := by
  execute fm 6

-- Phase E last: (a+1, 2, 0, 0, 0) ->* (a+2, 1, 0, 0, 0)
theorem phase_E_last : ⟨a+1, 2, 0, 0, 0⟩ [fm]⊢* ⟨a+2, 1, 0, 0, 0⟩ := by
  execute fm 6

-- Phase E full: (a+1, n+2, 0, 0, 0) ->* (a+n+2, 1, 0, 0, 0)
theorem phase_E : ∀ n, ∀ a, ⟨a+1, n+2, 0, 0, 0⟩ [fm]⊢* ⟨a+n+2, 1, 0, 0, 0⟩ := by
  intro n; induction' n with n ih <;> intro a
  · apply phase_E_last
  rw [show n + 1 + 2 = (n + 2) + 1 from by ring,
      show (n + 2 + 1 : ℕ) = n + 3 from by ring]
  apply stepStar_trans phase_E_inner
  apply stepStar_trans (ih _)
  ring_nf; finish

-- R4 chain: (j, 0, c, d, 0) ->* (0, 0, c+j, d+2*j, 0)
theorem r4_chain : ∀ j, ∀ c d, ⟨j, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c+j, d+2*j, 0⟩ := by
  intro j; induction' j with j ih <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase F: (a+1, 1, 0, 0, 0) ->* (0, 0, a, 2*a+2, 0)
theorem phase_F : ⟨a+1, 1, 0, 0, 0⟩ [fm]⊢* ⟨0, 0, a, 2*a+2, 0⟩ := by
  step fm; step fm
  apply stepStar_trans (r4_chain a 0 2)
  ring_nf; finish

-- Combined phases C through F: (2, 0, 0, 4*k+3, k+2) ->* (0, 0, 4*k+3, 8*k+8, 0)
theorem phases_C_to_F : ⟨2, 0, 0, 4*k+3, k+2⟩ [fm]⊢* ⟨0, 0, 4*k+3, 8*k+8, 0⟩ := by
  -- Phase C: (2, 0, 0, 4k+3, k+2) ->* (4k+5, 0, 0, 0, k+2)
  rw [show (2 : ℕ) = 1 + 1 from by ring, show (4*k+3 : ℕ) = 0 + (4*k+3) from by ring,
      show k + 2 = (k + 1) + 1 from by ring]
  apply stepStar_trans (r3r2_chain (4*k+3) 1 0 (e := k+1))
  rw [show 1 + (4*k+3) + 1 = (3*k+3) + (k+2) from by ring,
      show (k+1) + 1 = k + 2 from by ring,
      show (0 : ℕ) + (4*k+3) = 4*k+3 from by ring]
  -- Phase D: (4k+5, 0, 0, 0, k+2) ->* (3k+3, k+2, 0, 0, 0)
  apply stepStar_trans (r3_drain (k+2) (3*k+3) 0)
  rw [show (0 : ℕ) + (k + 2) = k + 2 from by ring]
  -- Phase E: (3k+3, k+2, 0, 0, 0) ->* (4k+4, 1, 0, 0, 0)
  rw [show 3 * k + 3 = (3 * k + 2) + 1 from by ring]
  apply stepStar_trans (phase_E k (3*k+2))
  -- Phase F: (4k+4, 1, 0, 0, 0) ->* (0, 0, 4k+3, 8k+8, 0)
  rw [show 3 * k + 2 + k + 2 = (4 * k + 3) + 1 from by ring]
  apply stepStar_trans phase_F
  rw [show 2 * (4 * k + 3) + 2 = 8 * k + 8 from by ring]
  finish

-- Main transition: (0, 0, 2*k+1, 4*k+4, 0) ->+ (0, 0, 4*k+3, 8*k+8, 0)
theorem main_trans : ⟨0, 0, 2*k+1, 4*k+4, 0⟩ [fm]⊢⁺ ⟨0, 0, 4*k+3, 8*k+8, 0⟩ := by
  -- Phase A: ->* (0, 1, 0, 4k+4, k+1)
  rw [show 4*k+4 = (4*k+3) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (phase_A k ((4*k+3)+1) 0)
  rw [show (0 : ℕ) + k + 1 = k + 1 from by ring]
  -- Phase B (R2): -> (2, 0, 0, 4k+3, k+2)
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  rw [show k + 1 + 1 = k + 2 from by ring, show (0 : ℕ) + 2 = 2 from by ring]
  -- Phases C-F
  exact phases_C_to_F

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 4, 0⟩) (by execute fm 16)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 2*k+1, 4*k+4, 0⟩) 0
  intro k
  exact ⟨2*k+1, by
    rw [show 2 * (2 * k + 1) + 1 = 4 * k + 3 from by ring,
        show 4 * (2 * k + 1) + 4 = 8 * k + 8 from by ring]
    exact main_trans⟩

end Sz22_2003_unofficial_40
