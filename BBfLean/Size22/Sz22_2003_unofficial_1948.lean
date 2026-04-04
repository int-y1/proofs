import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1948: [9/70, 55/2, 4/21, 7/11, 21/5]

Vector representation:
```
-1  2 -1 -1  0
-1  0  1  0  1
 2 -1  0 -1  0
 0  0  0  1 -1
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1948

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 repeated: (0, 0, c, d, k) ->* (0, 0, c, d+k, 0)
theorem r4_chain : ∀ k, ∀ d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih
  · intro d; exists 0
  · intro d
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih (d + 1)

-- Spiral: R2, R2, R4, R3 repeated
theorem spiral : ∀ k, ∀ b c e, ⟨2, b + k, c, 0, e⟩ [fm]⊢* ⟨2, b, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih
  · intro b c e; exists 0
  · intro b c e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm
    rw [show e + 2 = (e + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b (c + 2) (e + 1))
    ring_nf; finish

-- R1, R1, R3 drain cycle
theorem drain3 : ∀ k, ∀ b c d, ⟨2, b, c + 2 * k, 3 * k + d, 0⟩ [fm]⊢* ⟨2, b + 3 * k, c, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro b c d; simp; exists 0
  · intro b c d
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show 3 * (k + 1) + d = (3 * k + d) + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) c d)
    ring_nf; finish

-- Opening: R5, R3
theorem opening : ⟨0, 0, c + 1, d + 1, 0⟩ [fm]⊢⁺ ⟨2, 0, c, d + 1, 0⟩ := by
  step fm; step fm; finish

theorem opening_bc : ⟨0, b + 1, c + 1, 0, 0⟩ [fm]⊢⁺ ⟨2, b + 1, c, 0, 0⟩ := by
  step fm; step fm; finish

-- e_to_d + opening combined
theorem etod_opening : ⟨0, 0, c + 1, 0, k + 1⟩ [fm]⊢⁺ ⟨2, 0, c, k + 1, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (k + 1) 0 (c := c + 1)
    rw [show (0 : ℕ) + (k + 1) = k + 1 from by ring] at h
    exact h
  · exact opening (c := c) (d := k)

-- R2 step when d=0: (a+1, b, c, 0, e) -> (a, b, c+1, 0, e+1)
-- This is used when step fm fails due to symbolic c.
theorem r2_step_d0 : ⟨a + 1, b, c, 0, e⟩ [fm]⊢ ⟨a, b, c + 1, 0, e + 1⟩ := by
  simp [fm]

-- Phase A: (0, b+1, c+1, 0, 0) ->+ (0, 0, c+2b+4, 0, b+3)
theorem phaseA : ∀ b c, ⟨0, b + 1, c + 1, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * b + 4, 0, b + 3⟩ := by
  intro b c
  apply stepPlus_stepStar_stepPlus opening_bc
  rw [show b + 1 = 0 + (b + 1) from by ring]
  apply stepStar_trans (spiral (b + 1) 0 c 0)
  rw [show 0 + (b + 1) = b + 1 from by ring,
      show c + 2 * (b + 1) = c + 2 * b + 2 from by ring]
  -- State: (2, 0, c+2b+2, 0, b+1). R2 fires (a=2, d=0).
  apply stepStar_trans (step_stepStar r2_step_d0)
  -- State: (1, 0, c+2b+3, 0, b+2). R2 fires again.
  apply stepStar_trans (step_stepStar r2_step_d0)
  ring_nf; finish

-- Phase B mod 0: (0, 0, c+2k+1, 0, 3k) ->+ (2, 3k, c, 0, 0) [k >= 1]
theorem phaseB_mod0 (hk : k ≥ 1) :
    ⟨0, 0, c + 2 * k + 1, 0, 3 * k⟩ [fm]⊢⁺ ⟨2, 3 * k, c, 0, 0⟩ := by
  rw [show 3 * k = (3 * k - 1) + 1 from by omega]
  apply stepPlus_stepStar_stepPlus (etod_opening (c := c + 2 * k) (k := 3 * k - 1))
  rw [show 3 * k - 1 + 1 = 3 * k from by omega]
  have h := drain3 k 0 c 0
  rw [show (0 : ℕ) + 3 * k = 3 * k from by ring,
      show 3 * k + 0 = 3 * k from by ring] at h
  exact h

-- Phase B mod 2: (0, 0, c+2k+3, 0, 3k+2) ->+ (0, 3k+4, c, 0, 0)
theorem phaseB_mod2 : ∀ k c, ⟨0, 0, c + 2 * k + 3, 0, 3 * k + 2⟩ [fm]⊢⁺ ⟨0, 3 * k + 4, c, 0, 0⟩ := by
  intro k c
  rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (etod_opening (c := c + 2 * k + 2) (k := 3 * k + 1))
  rw [show 3 * k + 1 + 1 = 3 * k + 2 from by ring,
      show c + 2 * k + 2 = (c + 2) + 2 * k from by ring]
  have h := drain3 k 0 (c + 2) 2
  rw [show (0 : ℕ) + 3 * k = 3 * k from by ring] at h
  apply stepStar_trans h
  step fm; step fm; ring_nf; finish

-- Spiral close: (2, b, c, 0, 0) ->+ (0, 0, c+2b+2, 0, b+2)
theorem spiral_close : ∀ b c, ⟨2, b, c, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * b + 2, 0, b + 2⟩ := by
  intro b c
  rw [show b = 0 + b from by ring]
  apply stepStar_stepPlus_stepPlus (spiral b 0 c 0)
  rw [show 0 + b = b from by ring,
      show c + 2 * b = c + 2 * b from rfl]
  -- State: (2, 0, c+2b, 0, b). R2 fires (a=2, d=0).
  apply step_stepStar_stepPlus r2_step_d0
  apply stepStar_trans (step_stepStar r2_step_d0)
  ring_nf; finish

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨0, 6 * n + 7, 8 * n ^ 2 + 11 * n + 4, 0, 0⟩ [fm]⊢⁺
    ⟨0, 6 * n + 13, 8 * n ^ 2 + 27 * n + 23, 0, 0⟩ := by
  rw [show 6 * n + 7 = (6 * n + 6) + 1 from by ring,
      show 8 * n ^ 2 + 11 * n + 4 = (8 * n ^ 2 + 11 * n + 3) + 1 from by ring]
  -- Phase 1: phaseA
  apply stepPlus_stepStar_stepPlus (phaseA (6 * n + 6) (8 * n ^ 2 + 11 * n + 3))
  rw [show 8 * n ^ 2 + 11 * n + 3 + 2 * (6 * n + 6) + 4 = 8 * n ^ 2 + 23 * n + 19 from by ring,
      show 6 * n + 6 + 3 = 6 * n + 9 from by ring,
      show 8 * n ^ 2 + 23 * n + 19 = (8 * n ^ 2 + 19 * n + 12) + 2 * (2 * n + 3) + 1 from by ring,
      show 6 * n + 9 = 3 * (2 * n + 3) from by ring]
  -- Phase 2: phaseB_mod0
  apply stepStar_trans (stepPlus_stepStar
    (phaseB_mod0 (c := 8 * n ^ 2 + 19 * n + 12) (k := 2 * n + 3) (by omega)))
  rw [show 3 * (2 * n + 3) = 6 * n + 9 from by ring]
  -- Phase 3: spiral_close
  apply stepStar_trans (stepPlus_stepStar (spiral_close (6 * n + 9) (8 * n ^ 2 + 19 * n + 12)))
  rw [show 8 * n ^ 2 + 19 * n + 12 + 2 * (6 * n + 9) + 2 = 8 * n ^ 2 + 31 * n + 32 from by ring,
      show 6 * n + 9 + 2 = 6 * n + 11 from by ring,
      show 8 * n ^ 2 + 31 * n + 32 = (8 * n ^ 2 + 27 * n + 23) + 2 * (2 * n + 3) + 3 from by ring,
      show 6 * n + 11 = 3 * (2 * n + 3) + 2 from by ring,
      show 6 * n + 13 = 3 * (2 * n + 3) + 4 from by ring]
  -- Phase 4: phaseB_mod2
  exact stepPlus_stepStar (phaseB_mod2 (2 * n + 3) (8 * n ^ 2 + 27 * n + 23))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts
    (c₂ := ⟨0, 6 * 0 + 7, 8 * 0 ^ 2 + 11 * 0 + 4, 0, 0⟩) (by execute fm 48)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 6 * n + 7, 8 * n ^ 2 + 11 * n + 4, 0, 0⟩) 0
  intro n; exists n + 1
  show ⟨0, 6 * n + 7, 8 * n ^ 2 + 11 * n + 4, 0, 0⟩ [fm]⊢⁺
       ⟨0, 6 * (n + 1) + 7, 8 * (n + 1) ^ 2 + 11 * (n + 1) + 4, 0, 0⟩
  rw [show 6 * (n + 1) + 7 = 6 * n + 13 from by ring,
      show 8 * (n + 1) ^ 2 + 11 * (n + 1) + 4 = 8 * n ^ 2 + 27 * n + 23 from by ring]
  exact main_trans n
