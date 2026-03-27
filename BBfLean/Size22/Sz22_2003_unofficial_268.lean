import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #268: [14/15, 18/7, 1/18, 125/2, 7/5]

Vector representation:
```
 1 -1 -1  1
 1  2  0 -1
-1 -2  0  0
-1  0  3  0
 0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_268

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a+1, b+2, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

-- R4 phase: (k, 0, c, 0) ->* (0, 0, c+3k, 0)
theorem r4_phase : ∀ k c, ⟨k, 0, c, 0⟩ [fm]⊢* ⟨0, 0, c+3*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  step fm
  apply stepStar_trans (ih (c + 3))
  ring_nf; finish

-- Triple: (a, 0, c+2, d+1) ->* (a+3, 0, c, d+2) in 3 steps
theorem triple (a c d : ℕ) : ⟨a, 0, c+2, d+1⟩ [fm]⊢* ⟨a+3, 0, c, d+2⟩ := by
  step fm; step fm; step fm; finish

-- Triple chain: k iterations
theorem triple_chain : ∀ k a c d, ⟨a, 0, c+2*k, d+1⟩ [fm]⊢* ⟨a+3*k, 0, c, d+1+k⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
  apply stepStar_trans (ih a (c + 2) d)
  rw [show d + 1 + k = (d + k) + 1 from by ring]
  apply stepStar_trans (triple (a + 3 * k) c (d + k))
  rw [show a + 3 * k + 3 = a + 3 * (k + 1) from by ring,
      show d + k + 2 = d + 1 + (k + 1) from by ring]
  finish

-- R2 chain: (a, b, 0, k) ->* (a+k, b+2k, 0, 0)
theorem r2_chain : ∀ k a b, ⟨a, b, 0, k⟩ [fm]⊢* ⟨a+k, b+2*k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  step fm
  apply stepStar_trans (ih (a + 1) (b + 2))
  ring_nf; finish

-- R3 chain: (a+k, b+2k, 0, 0) ->* (a, b, 0, 0)
theorem r3_chain : ∀ k a b, ⟨a+k, b+2*k, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
  step fm
  exact ih a b

-- Cleanup: (a+1, 1, 0, 0) ->⁺ (a+4, 0, 0, 0)
theorem cleanup (a : ℕ) : ⟨a+1, 1, 0, 0⟩ [fm]⊢⁺ ⟨a+4, 0, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; finish

-- Mixing setup for odd case: (0, 0, 6m+3, 0) ->* (3, 0, 6m, 2)
theorem mixing_setup_odd (m : ℕ) : ⟨0, 0, 6*m+3, 0⟩ [fm]⊢* ⟨3, 0, 6*m, 2⟩ := by
  rw [show 6*m+3 = (6*m+2)+1 from by ring]
  step fm
  step fm
  rw [show 6*m+2 = (6*m+1)+1 from by ring]
  step fm
  rw [show 6*m+1 = (6*m)+1 from by ring]
  step fm; finish

-- Mixing setup for even case: (0, 0, 6m+6, 0) ->* (3, 0, 6m+3, 2)
theorem mixing_setup_even (m : ℕ) : ⟨0, 0, 6*m+6, 0⟩ [fm]⊢* ⟨3, 0, 6*m+3, 2⟩ := by
  rw [show 6*m+6 = (6*m+5)+1 from by ring]
  step fm
  step fm
  rw [show 6*m+5 = (6*m+4)+1 from by ring]
  step fm
  rw [show 6*m+4 = (6*m+3)+1 from by ring]
  step fm; finish

-- Even tail: (a, 0, c+1, d+1) -> R2 -> R1 -> (a+2, 1, c, d+1)
theorem even_tail (a c d : ℕ) : ⟨a, 0, c+1, d+1⟩ [fm]⊢* ⟨a+2, 1, c, d+1⟩ := by
  step fm; step fm; finish

-- Main transition for odd N = 2m+1 (m >= 0):
-- (2m+1, 0, 0, 0) ->+ (9m+3, 0, 0, 0)
theorem main_odd (m : ℕ) : ⟨2*m+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨9*m+3, 0, 0, 0⟩ := by
  -- R4 first step to get stepPlus
  apply step_stepStar_stepPlus
  · show fm ⟨2*m+1, 0, 0, 0⟩ = some ⟨2*m, 0, 3, 0⟩; simp [fm]
  -- R4 remaining: (2m, 0, 3, 0) ->* (0, 0, 3+6m, 0)
  apply stepStar_trans (r4_phase (2*m) 3)
  rw [show 3 + 3 * (2 * m) = 6 * m + 3 from by ring]
  -- Mixing setup: (0, 0, 6m+3, 0) ->* (3, 0, 6m, 2)
  apply stepStar_trans (mixing_setup_odd m)
  -- Triple chain k=3m: (3, 0, 6m, 2) ->* (9m+3, 0, 0, 3m+2)
  apply stepStar_trans
  · rw [show 6 * m = 0 + 2 * (3 * m) from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    have h := triple_chain (3*m) 3 0 1
    rw [show 3 + 3 * (3 * m) = 9 * m + 3 from by ring,
        show 1 + 1 + 3 * m = 3 * m + 2 from by ring] at h; exact h
  -- R2 chain: (9m+3, 0, 0, 3m+2) ->* (12m+5, 6m+4, 0, 0)
  apply stepStar_trans
  · have h := r2_chain (3*m+2) (9*m+3) 0
    rw [show 9*m+3+(3*m+2) = 12*m+5 from by ring,
        show 0 + 2*(3*m+2) = 6*m+4 from by ring] at h; exact h
  -- R3 chain: (12m+5, 6m+4, 0, 0) ->* (9m+3, 0, 0, 0)
  have h := r3_chain (3*m+2) (9*m+3) 0
  rw [show 9*m+3+(3*m+2) = 12*m+5 from by ring,
      show 0+2*(3*m+2) = 6*m+4 from by ring] at h; exact h

-- Main transition for even N = 2m+2 (m >= 0):
-- (2m+2, 0, 0, 0) ->+ (9m+11, 0, 0, 0)
theorem main_even (m : ℕ) : ⟨2*m+2, 0, 0, 0⟩ [fm]⊢⁺ ⟨9*m+11, 0, 0, 0⟩ := by
  -- R4 first step to get stepPlus
  apply step_stepStar_stepPlus
  · show fm ⟨2*m+2, 0, 0, 0⟩ = some ⟨2*m+1, 0, 3, 0⟩; simp [fm]
  -- R4 remaining
  apply stepStar_trans (r4_phase (2*m+1) 3)
  rw [show 3 + 3 * (2 * m + 1) = 6 * m + 6 from by ring]
  -- Mixing setup: (0, 0, 6m+6, 0) ->* (3, 0, 6m+3, 2)
  apply stepStar_trans (mixing_setup_even m)
  -- Triple chain k=3m+1: (3, 0, 6m+3, 2) ->* (9m+6, 0, 1, 3m+3)
  apply stepStar_trans
  · rw [show 6 * m + 3 = 1 + 2 * (3 * m + 1) from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    have h := triple_chain (3*m+1) 3 1 1
    rw [show 3 + 3 * (3 * m + 1) = 9 * m + 6 from by ring,
        show 1 + 1 + (3 * m + 1) = 3 * m + 3 from by ring] at h; exact h
  -- Even tail: (9m+6, 0, 1, 3m+3) ->* (9m+8, 1, 0, 3m+3)
  apply stepStar_trans
  · rw [show (1 : ℕ) = 0 + 1 from rfl, show 3 * m + 3 = (3 * m + 2) + 1 from by ring]
    have h := even_tail (9*m+6) 0 (3*m+2)
    rw [show 9*m+6+2 = 9*m+8 from by ring] at h; exact h
  -- R2 chain: (9m+8, 1, 0, 3m+3) ->* (12m+11, 6m+7, 0, 0)
  apply stepStar_trans
  · have h := r2_chain (3*m+3) (9*m+8) 1
    rw [show 9*m+8+(3*m+3) = 12*m+11 from by ring,
        show 1+2*(3*m+3) = 6*m+7 from by ring] at h; exact h
  -- R3 chain: (12m+11, 6m+7, 0, 0) ->* (9m+8, 1, 0, 0)
  apply stepStar_trans
  · have h := r3_chain (3*m+3) (9*m+8) 1
    rw [show 9*m+8+(3*m+3) = 12*m+11 from by ring,
        show 1+2*(3*m+3) = 6*m+7 from by ring] at h; exact h
  -- Cleanup: (9m+8, 1, 0, 0) ->⁺ (9m+11, 0, 0, 0)
  rw [show 9*m+8 = (9*m+7)+1 from by ring]
  have h := cleanup (9*m+7)
  rw [show 9*m+7+4 = 9*m+11 from by ring] at h
  exact stepPlus_stepStar h

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, 0⟩) 0
  intro n
  rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · rcases m with _ | m
    · omega
    rw [show n + 1 = 2*m+2 from by omega]
    exact ⟨9*m+10, main_even m⟩
  · rw [show n + 1 = 2*m+1 from by omega]
    exact ⟨9*m+2, main_odd m⟩

end Sz22_2003_unofficial_268
