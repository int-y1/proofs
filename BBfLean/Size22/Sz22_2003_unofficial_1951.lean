import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1951: [9/70, 55/2, 4/33, 7/11, 4/5]

Vector representation:
```
-1  2 -1 -1  0
-1  0  1  0  1
 2 -1  0  0 -1
 0  0  0  1 -1
 2  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1951

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

-- R4 repeated: move e to d. (0, 0, c, d, e+k) →* (0, 0, c, d+k, e).
theorem e_to_d : ∀ k, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

-- R5R1R1 drain: k rounds consuming 3 from c and 2 from d each round.
-- (0, b, c+3*k, 2*k+1, 0) →* (0, b+4*k, c, 1, 0)
theorem drain : ∀ k, ⟨0, b, c + 3 * k, 2 * k + 1, 0⟩ [fm]⊢* ⟨0, b + 4 * k, c, 1, 0⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm  -- R5
    step fm  -- R1
    step fm  -- R1
    apply stepStar_trans (ih (b := b + 4) (c := c))
    ring_nf; finish

-- Spiral: R3R2R2 repeated. (0, b+k, c, 0, e+1) →* (0, b, c+2*k, 0, e+k+1)
theorem spiral : ∀ k, ⟨0, b + k, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 2 * k, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R2
    step fm  -- R2
    apply stepStar_trans (ih (b := b) (c := c + 2) (e := e + 1))
    ring_nf; finish

-- Bridge: from (2, b, c, 1, 0) with case split on c.
theorem bridge : ⟨2, b, c, 1, 0⟩ [fm]⊢* ⟨0, b + 1, c + 2, 0, 2⟩ := by
  rcases c with _ | c
  · execute fm 5
  · execute fm 5

-- Full drain+bridge: (0, 0, c+3*k+1, 2*k+1, 0) →⁺ (0, 4*k+1, c+2, 0, 2)
theorem drain_bridge : ⟨0, 0, c + 3 * k + 1, 2 * k + 1, 0⟩ [fm]⊢⁺
    ⟨0, 4 * k + 1, c + 2, 0, 2⟩ := by
  rw [show c + 3 * k + 1 = (c + 1) + 3 * k from by ring]
  apply stepStar_stepPlus_stepPlus (drain k (b := 0) (c := c + 1))
  rw [show 0 + 4 * k = 4 * k from by ring]
  apply step_stepStar_stepPlus
    (show ⟨0, 4 * k, c + 1, 1, 0⟩ [fm]⊢ ⟨2, 4 * k, c, 1, 0⟩ from by simp [fm])
  exact bridge (b := 4 * k) (c := c)

-- Main transition: (0, 0, F+3*k+1, 0, 2*k+1) →⁺ (0, 0, F+8*k+4, 0, 4*k+3)
theorem main_trans : ⟨0, 0, F + 3 * k + 1, 0, 2 * k + 1⟩ [fm]⊢⁺
    ⟨0, 0, F + 8 * k + 4, 0, 4 * k + 3⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show (2 * k + 1 : ℕ) = 0 + (2 * k + 1) from by ring]
    exact e_to_d (2 * k + 1) (c := F + 3 * k + 1) (d := 0) (e := 0)
  rw [show 0 + (2 * k + 1) = 2 * k + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (drain_bridge (c := F) (k := k))
  rw [show (4 * k + 1 : ℕ) = 0 + (4 * k + 1) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (spiral (4 * k + 1) (b := 0) (c := F + 2) (e := 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, k⟩ ↦ ⟨0, 0, F + 3 * k + 1, 0, 2 * k + 1⟩) ⟨0, 0⟩
  intro ⟨F, k⟩; exact ⟨⟨2 * k + F, 2 * k + 1⟩, by
    show ⟨0, 0, F + 3 * k + 1, 0, 2 * k + 1⟩ [fm]⊢⁺
      ⟨0, 0, (2 * k + F) + 3 * (2 * k + 1) + 1, 0, 2 * (2 * k + 1) + 1⟩
    rw [show (2 * k + F) + 3 * (2 * k + 1) + 1 = F + 8 * k + 4 from by ring,
        show 2 * (2 * k + 1) + 1 = 4 * k + 3 from by ring]
    exact main_trans⟩
