import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #144: [1/45, 22/35, 65/2, 147/13, 5/33]

Vector representation:
```
 0 -2 -1  0  0  0
 1  0 -1 -1  1  0
-1  0  1  0  0  1
 0  1  0  2  0 -1
 0 -1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_144

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+2, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- Phase 1: R3/R2 loop, consuming d and producing e and f.
theorem r3r2_loop : ∀ k d e f,
    ⟨1, 0, 0, d + k, e, f⟩ [fm]⊢* ⟨(1 : ℕ), 0, 0, d, e + k, f + k⟩ := by
  intro k; induction k with
  | zero => intro d e f; exists 0
  | succ k ih =>
    intro d e f
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih d (e + 1) (f + 1))
    ring_nf; finish

-- Phase 2: Bridge (8 steps).
theorem bridge : ∀ e f,
    ⟨1, 0, 0, 0, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, 2, e + 2, f + 1⟩ := by
  intro e f
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  finish

-- Phase 3: R4 loop, converting f to b and d.
theorem r4_loop : ∀ k b d e f,
    ⟨0, b, 0, d, e, f + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d + 2 * k, e, f⟩ := by
  intro k; induction k with
  | zero => intro b d e f; exists 0
  | succ k ih =>
    intro b d e f
    rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) (d + 2) e f)
    ring_nf; finish

-- Phase 4: R5+R1 drain loop.
theorem drain_loop : ∀ k b d e,
    ⟨0, b + 3 * k, 0, d, e + k, 0⟩ [fm]⊢* ⟨(0 : ℕ), b, 0, d, e, 0⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show b + 3 * (k + 1) = (b + 3 * k + 2) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show b + 3 * k + 2 = (b + 3 * k) + 2 from by ring]
    step fm
    exact ih b d e

-- Phase 5: Final R5 + R2.
theorem final_steps : ∀ d e,
    ⟨0, 1, 0, d + 1, e + 1, 0⟩ [fm]⊢* ⟨(1 : ℕ), 0, 0, d, e + 1, 0⟩ := by
  intro d e; step fm; step fm; finish

-- Main transition: canonical state (1, 0, 0, 3(n+1), 2(n+1), 0) progresses.
theorem main_trans (n : ℕ) :
    ⟨1, 0, 0, 3 * n + 3, 2 * n + 2, 0⟩ [fm]⊢⁺
    ⟨(1 : ℕ), 0, 0, 6 * n + 9, 4 * n + 6, 0⟩ := by
  -- Phase 1: R3/R2 loop (3n+3 iterations)
  -- (1, 0, 0, 3n+3, 2n+2, 0) →* (1, 0, 0, 0, 5n+5, 3n+3)
  apply step_stepStar_stepPlus
    (c₂ := ⟨0, 0, 1, 3 * n + 3, 2 * n + 2, 1⟩)
  · show fm ⟨0 + 1, 0, 0, 3 * n + 3, 2 * n + 2, 0⟩ =
         some ⟨0, 0, 1, 3 * n + 3, 2 * n + 2, 1⟩
    simp [fm]
  -- R2 step
  rw [show 3 * n + 3 = (3 * n + 2) + 1 from by ring]
  apply stepStar_trans
    (c₂ := ⟨1, 0, 0, 3 * n + 2, 2 * n + 3, 1⟩)
  · step fm; finish
  -- Remaining R3/R2 loop (3n+2 iterations)
  apply stepStar_trans
    (c₂ := ⟨1, 0, 0, 0, 5 * n + 5, 3 * n + 3⟩)
  · rw [show 3 * n + 2 = 0 + (3 * n + 2) from by ring]
    have h := r3r2_loop (3 * n + 2) 0 (2 * n + 3) 1
    rw [show 2 * n + 3 + (3 * n + 2) = 5 * n + 5 from by ring,
        show 1 + (3 * n + 2) = 3 * n + 3 from by ring] at h
    exact h
  -- Phase 2: Bridge
  apply stepStar_trans
    (c₂ := ⟨0, 0, 0, 2, 5 * n + 7, 3 * n + 4⟩)
  · have h := bridge (5 * n + 5) (3 * n + 3)
    rw [show 5 * n + 5 + 2 = 5 * n + 7 from by ring,
        show 3 * n + 3 + 1 = 3 * n + 4 from by ring] at h
    exact h
  -- Phase 3: R4 loop (3n+4 iterations)
  apply stepStar_trans
    (c₂ := ⟨0, 3 * n + 4, 0, 6 * n + 10, 5 * n + 7, 0⟩)
  · have h := r4_loop (3 * n + 4) 0 2 (5 * n + 7) 0
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * (3 * n + 4) = 6 * n + 10 from by ring] at h
    exact h
  -- Phase 4: Drain loop (n+1 iterations)
  apply stepStar_trans
    (c₂ := ⟨0, 1, 0, 6 * n + 10, 4 * n + 6, 0⟩)
  · rw [show 3 * n + 4 = 1 + 3 * (n + 1) from by ring,
        show 5 * n + 7 = 4 * n + 6 + (n + 1) from by ring]
    exact drain_loop (n + 1) 1 (6 * n + 10) (4 * n + 6)
  -- Phase 5: Final R5 + R2
  · rw [show 6 * n + 10 = (6 * n + 9) + 1 from by ring,
        show 4 * n + 6 = (4 * n + 5) + 1 from by ring]
    have h := final_steps (6 * n + 9) (4 * n + 5)
    rw [show 4 * n + 5 + 1 = 4 * n + 6 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 3, 2, 0⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, 3 * (n + 1), 2 * (n + 1), 0⟩) 0
  intro n
  refine ⟨2 * n + 2, ?_⟩
  show ⟨1, 0, 0, 3 * (n + 1), 2 * (n + 1), 0⟩ [fm]⊢⁺
       ⟨1, 0, 0, 3 * (2 * n + 2 + 1), 2 * (2 * n + 2 + 1), 0⟩
  rw [show 3 * (n + 1) = 3 * n + 3 from by ring,
      show 2 * (n + 1) = 2 * n + 2 from by ring,
      show 3 * (2 * n + 2 + 1) = 6 * n + 9 from by ring,
      show 2 * (2 * n + 2 + 1) = 4 * n + 6 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_144
