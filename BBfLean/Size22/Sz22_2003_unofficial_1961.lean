import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1961: [99/35, 1/5, 10/3, 49/2, 1/77, 5/7]

Vector representation:
```
 0  2 -1 -1  1
 0  0 -1  0  0
 1 -1  1  0  0
-1  0  0  2  0
 0  0  0 -1 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1961

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3+R1 interleaved chain: each pair does a+1, b+1, d-1, e+1.
theorem r3r1_chain : ∀ k a b e, ⟨a, b + 1, 0, k, e⟩ [fm]⊢* ⟨a + k, b + 1 + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · step fm  -- R3: (a+1, b, 1, k+1, e)
    step fm  -- R1: (a+1, b+2, 0, k, e+1)
    apply stepStar_trans (ih (a + 1) (b + 1) (e + 1))
    ring_nf; finish

-- R3+R2 drain: convert b to a. Each R3+R2 pair: a+1, b-1.
theorem r3r2_drain : ∀ k a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm  -- R3: (a+1, k, 1, 0, e)
    step fm  -- R2: (a+1, k, 0, 0, e)
    apply stepStar_trans (ih (a + 1) e)
    ring_nf; finish

-- R4 chain: convert a to d.
theorem r4_chain : ∀ a d e, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * a, e⟩ := by
  intro a; induction' a with a ih <;> intro d e
  · exists 0
  · step fm  -- R4: (a, 0, 0, d+2, e)
    apply stepStar_trans (ih (d + 2) e)
    ring_nf; finish

-- R5 chain: drain d and e together.
theorem r5_chain : ∀ k d, ⟨0, 0, 0, d + k, k⟩ [fm]⊢* ⟨0, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · apply stepStar_trans
    · show ⟨0, 0, 0, d + (k + 1), k + 1⟩ [fm]⊢* ⟨0, 0, 0, d + k, k⟩
      step fm; finish
    · exact ih d

-- Main transition: (0, 0, 0, d+2, 0) ->+ (0, 0, 0, 3*d+3, 0)
theorem main_trans : ∀ d, ⟨0, 0, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * d + 3, 0⟩ := by
  intro d
  -- Phase 1: R6
  step fm  -- (0, 0, 1, d+1, 0)
  -- Phase 2: R1
  step fm  -- (0, 2, 0, d, 1)
  -- Phase 3: R3+R1 chain: (0, 2, 0, d, 1) ->* (d, d+2, 0, 0, d+1)
  apply stepStar_trans (r3r1_chain d 0 1 1)
  -- Phase 4: R3+R2 drain: (d, d+2, 0, 0, d+1) ->* (2d+2, 0, 0, 0, d+1)
  apply stepStar_trans (r3r2_drain (1 + 1 + d) (0 + d) (1 + d))
  -- Phase 5: R4 chain: (2d+2, 0, 0, 0, d+1) ->* (0, 0, 0, 4d+4, d+1)
  apply stepStar_trans (r4_chain (0 + d + (1 + 1 + d)) 0 (1 + d))
  -- Phase 6: R5 chain: (0, 0, 0, 4d+4, d+1) ->* (0, 0, 0, 3d+3, 0)
  rw [show 0 + 2 * (0 + d + (1 + 1 + d)) = (3 * d + 3) + (1 + d) from by ring]
  apply stepStar_trans (r5_chain (1 + d) (3 * d + 3))
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0 + 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, 0⟩) 0
  intro n; exists 3 * n + 1
  rw [show 3 * n + 1 + 2 = 3 * n + 3 from by ring]
  exact main_trans n
