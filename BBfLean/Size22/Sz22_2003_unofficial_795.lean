import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #795: [35/6, 605/2, 4/77, 3/5, 35/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_795

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 chain: move c to b when a=0 and d=0.
theorem c_to_b : ∀ k b c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c e)
    ring_nf; finish

-- Inner spiral: each round is R3, R1, R1.
theorem spiral_chain : ∀ k b c d e, ⟨0, b + 2 * k, c, d + 1, e + k⟩ [fm]⊢*
    ⟨0, b, c + 2 * k, d + k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R1
    step fm  -- R1
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih b (c + 2) (d + 1) e)
    ring_nf; finish

-- Tail for odd b: R3, R1, R2.
theorem tail_odd : ⟨0, 1, c, d + 1, e + 1⟩ [fm]⊢* ⟨0, 0, c + 2, d + 1, e + 2⟩ := by
  step fm; step fm; step fm; finish

-- Drain: R3, R2, R2 repeated.
theorem drain : ∀ k c e, ⟨0, 0, c, k, e + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + 1 + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm  -- R3
    step fm  -- R2
    step fm  -- R2
    rw [show c + 1 + 1 = c + 2 from by ring,
        show e + 2 + 2 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (c + 2) (e + 3))
    ring_nf; finish

-- Phases 2-5 as ⊢*.
theorem phases_2_to_5 (m r : ℕ) :
    ⟨0, 2 * m + 1, 0, 0, m + r + 2⟩ [fm]⊢* ⟨0, 0, 4 * m + 5, 0, 3 * m + r + 5⟩ := by
  -- R5 step.
  rw [show m + r + 2 = (m + r + 1) + 1 from by ring]
  step fm
  -- Spiral chain with k = m.
  rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      show m + r + 1 = (r + 1) + m from by ring]
  apply stepStar_trans (spiral_chain m 1 1 0 (r + 1))
  -- Tail odd.
  rw [show 1 + 2 * m = 2 * m + 1 from by ring,
      show 0 + m + 1 = m + 0 + 1 from by ring,
      show (r + 1 : ℕ) = r + 0 + 1 from by ring]
  apply stepStar_trans (tail_odd (c := 2 * m + 1) (d := m + 0) (e := r + 0))
  -- Drain with k = m+1.
  rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
      show m + 0 + 1 = m + 1 from by ring,
      show r + 0 + 2 = (r + 1) + 1 from by ring]
  apply stepStar_trans (drain (m + 1) (2 * m + 3) (r + 1))
  ring_nf; finish

-- Main transition as ⊢⁺.
theorem main_trans (m r : ℕ) :
    ⟨0, 0, 2 * m + 1, 0, m + r + 2⟩ [fm]⊢⁺ ⟨0, 0, 4 * m + 5, 0, 3 * m + r + 5⟩ := by
  -- Phase 1: first R4 step to establish ⊢⁺.
  rw [show (2 * m + 1 : ℕ) = 2 * m + 0 + 1 from by ring]
  step fm
  -- Remaining R4 steps.
  rw [show (2 * m : ℕ) = 0 + 2 * m from by ring]
  apply stepStar_trans (c_to_b (2 * m) 1 0 (m + r + 2))
  rw [show 1 + 2 * m = 2 * m + 1 from by ring]
  -- Phases 2-5.
  exact phases_2_to_5 m r

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, r⟩ ↦ ⟨0, 0, 2 * m + 1, 0, m + r + 2⟩) ⟨0, 0⟩
  intro ⟨m, r⟩
  refine ⟨⟨2 * m + 2, m + r + 1⟩, ?_⟩
  show ⟨0, 0, 2 * m + 1, 0, m + r + 2⟩ [fm]⊢⁺
    ⟨0, 0, 2 * (2 * m + 2) + 1, 0, (2 * m + 2) + (m + r + 1) + 2⟩
  rw [show 2 * (2 * m + 2) + 1 = 4 * m + 5 from by ring,
      show (2 * m + 2) + (m + r + 1) + 2 = 3 * m + r + 5 from by ring]
  exact main_trans m r
