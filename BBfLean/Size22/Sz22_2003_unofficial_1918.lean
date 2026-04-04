import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1918: [9/70, 1/33, 4/3, 55/2, 147/11]

Vector representation:
```
-1  2 -1 -1  0
 0 -1  0  0 -1
 2 -1  0  0  0
-1  0  1  0  1
 0  1  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1918

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R4 chain with d=0: (k, 0, c, 0, e) ->* (0, 0, c+k, 0, e+k)
theorem r4_chain : ∀ k, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · apply stepStar_trans (step_stepStar (c₂ := ⟨k, 0, c + 1, 0, e + 1⟩) (by simp [fm]))
    apply stepStar_trans (ih (c := c + 1) (e := e + 1))
    ring_nf; finish

-- e_drain for odd e: (0, 0, c, d, 2k+1) ->* (2, 0, c, d+2k+2, 0)
theorem e_drain : ∀ k, ⟨0, 0, c, d, 2 * k + 1⟩ [fm]⊢* ⟨2, 0, c, d + 2 * k + 2, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

-- One round: R1, R1, R3
theorem one_round : ⟨2, b, c + 1 + 1, d + 1 + 1, 0⟩ [fm]⊢⁺ ⟨2, b + 3, c, d, 0⟩ := by
  step fm; step fm; step fm; finish

-- Round chain by induction
theorem round_chain : ∀ k, ⟨2, b, c + 2 * k, d + 2 * k, 0⟩ [fm]⊢* ⟨2, b + 3 * k, c, d, 0⟩ := by
  intro k; induction' k with k ih generalizing b c d
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 1 + 1 from by ring]
    apply stepStar_trans (stepPlus_stepStar (one_round (b := b) (c := c + 2 * k) (d := d + 2 * k)))
    apply stepStar_trans (ih (b := b + 3))
    ring_nf; finish

-- R3 drain: (a, k, 0, d, 0) ->* (a+2k, 0, 0, d, 0)
theorem r3_drain : ∀ k, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

-- Cleanup: (a+2, 0, 0, 1, 0) -> (a+2, 0, 0, 0, 0) in 4 steps
theorem cleanup : ⟨a + 1 + 1, 0, 0, 1, 0⟩ [fm]⊢⁺ ⟨a + 1 + 1, 0, 0, 0, 0⟩ := by
  execute fm 4

-- Main transition: (2m+1, 0, 0, 0, 0) ->+ (6m+5, 0, 0, 0, 0)
theorem main_trans : ∀ m, ⟨2 * m + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨6 * m + 5, 0, 0, 0, 0⟩ := by
  intro m
  -- Phase 1: R4 chain: (2m+1, 0, 0, 0, 0) ->* (0, 0, 2m+1, 0, 2m+1)
  have h1 : ⟨2 * m + 1, 0, 0, 0, 0⟩ [fm]⊢* ⟨0, 0, 2 * m + 1, 0, 2 * m + 1⟩ := by
    have := r4_chain (2 * m + 1) (c := 0) (e := 0)
    simpa using this
  -- Phase 2: e_drain: (0, 0, 2m+1, 0, 2m+1) ->* (2, 0, 2m+1, 2m+2, 0)
  have h2 : ⟨0, 0, 2 * m + 1, 0, 2 * m + 1⟩ [fm]⊢* ⟨2, 0, 2 * m + 1, 2 * m + 2, 0⟩ := by
    have := e_drain m (c := 2 * m + 1) (d := 0)
    simpa using this
  -- Phase 3: round_chain: (2, 0, 2m+1, 2m+2, 0) ->* (2, 3m, 1, 2, 0)
  have h3 : ⟨2, 0, 2 * m + 1, 2 * m + 2, 0⟩ [fm]⊢* ⟨2, 3 * m, 1, 2, 0⟩ := by
    have := round_chain m (b := 0) (c := 1) (d := 2)
    rw [show 1 + 2 * m = 2 * m + 1 from by ring,
        show 2 + 2 * m = 2 * m + 2 from by ring,
        show 0 + 3 * m = 3 * m from by ring] at this
    exact this
  -- Phase 4: R1: (2, 3m, 1, 2, 0) -> (1, 3m+2, 0, 1, 0)
  have h4 : (⟨2, 3 * m, 1, 2, 0⟩ : Q) [fm]⊢ ⟨1, 3 * m + 2, 0, 1, 0⟩ := by simp [fm]
  -- Phase 5: R3 drain: (1, 3m+2, 0, 1, 0) ->* (6m+5, 0, 0, 1, 0)
  have h5 : ⟨1, 3 * m + 2, 0, 1, 0⟩ [fm]⊢* ⟨6 * m + 5, 0, 0, 1, 0⟩ := by
    have := r3_drain (3 * m + 2) (a := 1) (d := 1)
    rw [show 1 + 2 * (3 * m + 2) = 6 * m + 5 from by ring] at this
    exact this
  -- Phase 6: cleanup: (6m+5, 0, 0, 1, 0) ->+ (6m+5, 0, 0, 0, 0)
  have h6 : ⟨6 * m + 5, 0, 0, 1, 0⟩ [fm]⊢⁺ ⟨6 * m + 5, 0, 0, 0, 0⟩ := by
    rw [show 6 * m + 5 = (6 * m + 3) + 1 + 1 from by ring]
    exact cleanup
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepStar_stepPlus_stepPlus h3
        (step_stepPlus_stepPlus h4
          (stepStar_stepPlus_stepPlus h5 h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨2 * m + 1, 0, 0, 0, 0⟩) 2
  intro m
  refine ⟨3 * m + 2, ?_⟩
  rw [show 2 * (3 * m + 2) + 1 = 6 * m + 5 from by ring]
  exact main_trans m
