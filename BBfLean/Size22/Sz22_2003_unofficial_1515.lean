import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1515: [7/15, 99/14, 22/3, 5/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  1
 1 -1  0  0  1
 0  0  1  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1515

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: convert e to c.
theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + 2 * k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (c := c) (e := e + 2))
    step fm
    rw [show c + k + 1 = c + (k + 1) from by ring]
    finish

-- Spiral loop: R2,R1,R1 repeated.
theorem spiral_loop : ∀ m, ⟨m + 1, 0, 2 * m + 1, d + 1, e⟩ [fm]⊢* ⟨1, 0, 1, d + m + 1, e + m⟩ := by
  intro m; induction' m with m ih generalizing d e
  · exists 0
  · rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 1) (e := e + 1))
    ring_nf; finish

-- End of spiral: R2, R1, R3.
theorem spiral_end : ⟨1, 0, 1, d + 1, e⟩ [fm]⊢* ⟨1, 0, 0, d + 1, e + 2⟩ := by
  step fm; step fm; step fm; finish

-- R2+R3 interleaving: drain d while growing b.
theorem r2r3_loop : ∀ k j e, ⟨1, j, 0, k, e⟩ [fm]⊢* ⟨1, j + k, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro j e
  · ring_nf; exists 0
  · apply stepStar_trans (step_stepStar (c₂ := ⟨0, j + 2, 0, k, e + 1⟩) (by simp [fm]))
    apply stepStar_trans (step_stepStar (c₂ := ⟨1, j + 1, 0, k, e + 2⟩) (by simp [fm]))
    apply stepStar_trans (ih (j + 1) (e + 2))
    ring_nf; finish

-- R3 chain: drain b to a.
theorem r3_chain : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    apply stepStar_trans (ih (a := a) (b := b + 1) (e := e))
    step fm
    ring_nf; finish

-- Full transition: (n+2, 0, 0, 0, 4n+4) →⁺ (n+3, 0, 0, 0, 4n+8)
theorem main_transition : ⟨n + 2, 0, 0, 0, 4 * n + 4⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 4 * n + 8⟩ := by
  -- Phase 1: R4 chain. (n+2, 0, 0, 0, 4n+4) →* (n+2, 0, 2n+2, 0, 0)
  rw [show (4 * n + 4 : ℕ) = 0 + 2 * (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * n + 2) (a := n + 2) (c := 0) (e := 0))
  rw [show (0 : ℕ) + (2 * n + 2) = 2 * n + 2 from by ring]
  -- Phase 2a: R5 step.
  step fm  -- R5: (n+1, 1, 2n+2, 1, 0)
  -- Phase 2b: R1 step.
  step fm  -- R1: (n+1, 0, 2n+1, 2, 0)
  -- Phase 2c: Spiral loop. Need to rewrite 2 as 1+1.
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (spiral_loop n (d := 1) (e := 0))
  rw [show 1 + n + 1 = (n + 1) + 1 from by ring, show (0 : ℕ) + n = n from by ring]
  -- Phase 2d: Spiral end.
  apply stepStar_trans (spiral_end (d := n + 1) (e := n))
  rw [show (n + 1 + 1 : ℕ) = n + 2 from by ring]
  -- Phase 3: R2+R3 loop.
  apply stepStar_trans (r2r3_loop (n + 2) 0 (n + 2))
  rw [show (0 : ℕ) + (n + 2) = n + 2 from by ring,
      show n + 2 + 2 * (n + 2) = 3 * n + 6 from by ring]
  -- Phase 4: R3 chain.
  rw [show (n + 2 : ℕ) = 0 + (n + 2) from by ring]
  apply stepStar_trans (r3_chain (n + 2) (a := 1) (b := 0) (e := 3 * n + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 4⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 4 * n + 4⟩) 0
  intro n; exists n + 1
  rw [show 4 * (n + 1) + 4 = 4 * n + 8 from by ring]
  exact main_transition
