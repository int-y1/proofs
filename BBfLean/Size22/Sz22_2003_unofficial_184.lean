import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #184: [1/6, 175/2, 26/77, 33/5, 4/39]

Vector representation:
```
-1 -1  0  0  0  0
-1  0  2  1  0  0
 1  0  0 -1 -1  1
 0  1 -1  0  1  0
 2 -1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_184

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d+1, e, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | _ => none

-- R5/R1 chain: (0, 3k+1, 0, 0, e, f+k) ->* (0, 1, 0, 0, e, f)
theorem r5r1_chain : ∀ k e f,
    ⟨0, 3*k+1, 0, 0, e, f+k⟩ [fm]⊢* ⟨(0 : ℕ), 1, 0, 0, e, f⟩ := by
  intro k; induction' k with k h <;> intro e f
  · exists 0
  rw [show 3 * (k + 1) + 1 = (3 * k + 3) + 1 from by ring,
      show f + (k + 1) = (f + k) + 1 from by ring]
  step fm
  rw [show 3 * k + 3 = (3 * k + 2) + 1 from by ring]
  step fm
  rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3/R2 interleaved loop: consume e, build c and f
-- (0, 0, c, 2, j, f) ->* (0, 0, c+2j, 2, 0, f+j)
theorem r3r2_chain : ∀ j c f,
    ⟨0, 0, c, 2, j, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c+2*j, 2, 0, f+j⟩ := by
  intro j; induction' j with j h <;> intro c f
  · exists 0
  rw [show (j + 1) = j + 1 from rfl]
  step fm
  step fm
  apply stepStar_trans (h (c + 2) (f + 1))
  ring_nf; finish

-- Tail + R4 combined: (0, 0, c+2, 2, 0, f) ->* (0, c, 0, 0, c, f+2)
theorem tail_and_r4 : ∀ c f,
    ⟨0, 0, c+2, 2, 0, f⟩ [fm]⊢* ⟨(0 : ℕ), c, 0, 0, c, f+2⟩ := by
  intro c f
  -- 6 fixed steps: (0, 0, c+2, 2, 0, f) -> (0, 0, c, 0, 0, f+2)
  step fm
  step fm
  step fm
  step fm
  step fm
  step fm
  -- R4 loop: (0, 0, c, 0, 0, f+2) ->* (0, c, 0, 0, c, f+2)
  suffices h : ∀ j b e g, ⟨0, b, j, 0, e, g⟩ [fm]⊢* ⟨(0 : ℕ), b+j, 0, 0, e+j, g⟩ from by
    have := h c 0 0 (f + 2)
    simp only [Nat.zero_add] at this
    exact this
  intro j; induction' j with j ih <;> intro b e g
  · exists 0
  step fm
  apply stepStar_trans (ih (b + 1) (e + 1) g)
  ring_nf; finish

-- Main transition: (0, 3k+1, 0, 0, 3k+1, 2k+1) →⁺ (0, 6k+4, 0, 0, 6k+4, 4k+3)
theorem main_trans (k : ℕ) :
    ⟨0, 3*k+1, 0, 0, 3*k+1, 2*k+1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 6*k+4, 0, 0, 6*k+4, 4*k+3⟩ := by
  -- Phase 1: R5/R1 chain to (0, 1, 0, 0, 3k+1, k+1)
  rw [show 2 * k + 1 = (k + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain k (3*k+1) (k+1))
  -- R5 final + R2 pair: (0, 1, 0, 0, 3k+1, k+1) -> (0, 0, 4, 2, 3k+1, k) in 3 steps
  rw [show k + 1 = k + 1 from rfl]
  step fm
  step fm
  step fm
  -- Phase 3: R3/R2 chain
  apply stepStar_trans (r3r2_chain (3*k+1) 4 k)
  -- Now at (0, 0, 4+2*(3k+1), 2, 0, k+(3k+1))
  rw [show 4 + 2 * (3 * k + 1) = (6 * k + 4) + 2 from by ring,
      show k + (3 * k + 1) = 4 * k + 1 from by ring]
  -- Phase 4+5: tail + R4 loop
  apply stepStar_trans (tail_and_r4 (6*k+4) (4*k+1))
  rw [show 4 * k + 1 + 2 = 4 * k + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 4, 0, 0, 4, 3⟩) (by execute fm 20)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 3*(n+1)+1, 0, 0, 3*(n+1)+1, 2*(n+1)+1⟩) 0
  intro n
  exists 2*n + 2
  have h := main_trans (n + 1)
  simp only [(show 6 * (n + 1) + 4 = 3 * (2 * n + 2 + 1) + 1 from by ring),
             (show 4 * (n + 1) + 3 = 2 * (2 * n + 2 + 1) + 1 from by ring)] at h
  exact h

end Sz22_2003_unofficial_184
