import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1550: [7/30, 6/77, 121/2, 25/11, 14/5]

Vector representation:
```
-1 -1 -1  1  0
 1  1  0 -1 -1
-1  0  0  0  2
 0  0  2  0 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1550

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R2,R2,R3 chain: k rounds.
theorem r2r2r3_chain : ∀ k j d,
    ⟨j, 2 * j, 0, d + 2 * k, 2⟩ [fm]⊢* ⟨j + k, 2 * (j + k), 0, d, 2⟩ := by
  intro k; induction' k with k ih <;> intro j d
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans
      (step_stepStar (show ⟨j+1+1, 2*j+1+1, 0, d+2*k, 0⟩ [fm]⊢
        ⟨j+1, 2*j+1+1, 0, d+2*k, 2⟩ from by simp [fm]))
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) from by ring]
    apply stepStar_trans (ih (j + 1) d)
    ring_nf; finish

-- R3 drain.
theorem r3_drain : ∀ k a b e,
    ⟨a + k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (e + 2))
    ring_nf; finish

-- R4 chain.
theorem r4_chain : ∀ k b c e,
    ⟨0, b, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 2) e)
    ring_nf; finish

-- R5,R1 chain.
theorem r5r1_chain : ∀ k b c d,
    ⟨0, b + k, c + 2 * k, d, 0⟩ [fm]⊢* ⟨0, b, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b c (d + 2))
    ring_nf; finish

-- Tail: (0, 0, 4, D, 0) ⊢⁺ (1, 0, 0, D+2, 0).
theorem tail (D : ℕ) : ⟨0, 0, 4, D, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, D + 2, 0⟩ := by
  step fm
  apply stepStar_trans
    (step_stepStar (show ⟨1, 0, 3, D+1, 0⟩ [fm]⊢ ⟨0, 0, 3, D+1, 2⟩ from by simp [fm]))
  apply stepStar_trans
    (step_stepStar (show ⟨0, 0, 3, D+1, 2⟩ [fm]⊢ ⟨1, 1, 3, D, 1⟩ from by simp [fm]))
  step fm
  apply stepStar_trans
    (step_stepStar (show ⟨0, 0, 2, D+1, 1⟩ [fm]⊢ ⟨1, 1, 2, D, 0⟩ from by simp [fm]))
  step fm
  apply stepStar_trans
    (step_stepStar (show ⟨0, 0, 1, D+1, 0⟩ [fm]⊢ ⟨1, 0, 0, D+2, 0⟩ from by simp [fm]))
  finish

-- Main transition.
theorem main_trans (n : ℕ) :
    ⟨1, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 4 * n + 6, 0⟩ := by
  -- Phase 1: R3 (symbolic d)
  apply step_stepStar_stepPlus
  · show fm ⟨1, 0, 0, 2 * n + 2, 0⟩ = some ⟨0, 0, 0, 2 * n + 2, 2⟩; simp [fm]
  -- Phase 2: R2,R2,R3 chain (n rounds)
  rw [show 2 * n + 2 = 2 + 2 * n from by ring]
  apply stepStar_trans (r2r2r3_chain n 0 2)
  simp only [Nat.zero_add]
  -- Phase 3: Two R2 steps: (n, 2*n, 0, 2, 2) → (n+2, 2*n+2, 0, 0, 0)
  step fm; step fm
  -- Phase 4: R3 drain (n+2 steps)
  -- State: (n+1+1, 2*n+1+1, 0, 0, 0)
  -- Need: (0+(n+2), 2*n+2, 0, 0, 0)
  have phase4 := r3_drain (n + 2) 0 (2 * n + 2) 0
  rw [show (0 : ℕ) + (n + 2) = n + 1 + 1 from by ring,
      show 0 + 2 * (n + 2) = 2 * n + 4 from by ring] at phase4
  rw [show 2 * n + 1 + 1 = 2 * n + 2 from by ring]
  apply stepStar_trans phase4
  -- Phase 5: R4 chain
  -- State: (0, 2*n+2, 0, 0, 2*n+4)
  have phase5 := r4_chain (2 * n + 4) (2 * n + 2) 0 0
  rw [show (0 : ℕ) + (2 * n + 4) = 2 * n + 4 from by ring,
      show 0 + 2 * (2 * n + 4) = 4 * n + 8 from by ring] at phase5
  apply stepStar_trans phase5
  -- Phase 6: R5,R1 chain
  -- State: (0, 2*n+2, 4*n+8, 0, 0)
  have phase6 := r5r1_chain (2 * n + 2) 0 4 0
  rw [show (0 : ℕ) + (2 * n + 2) = 2 * n + 2 from by ring,
      show 4 + 2 * (2 * n + 2) = 4 * n + 8 from by ring,
      show 0 + 2 * (2 * n + 2) = 4 * n + 4 from by ring] at phase6
  apply stepStar_trans phase6
  -- Phase 7: Tail
  -- State: (0, 0, 4, 4*n+4, 0)
  exact stepPlus_stepStar (tail (4 * n + 4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 0⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, 2 * n + 2, 0⟩) 0
  intro n; refine ⟨2 * n + 2, ?_⟩
  rw [show 2 * (2 * n + 2) + 2 = 4 * n + 6 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1550
