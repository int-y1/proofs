import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #222: [105/2, 1/363, 10/39, 143/5, 3/77]

Vector representation:
```
-1  1  1  1  0  0
 0 -1  0  0 -2  0
 1 -1  1  0  0 -1
 0  0 -1  0  1  1
 0  1  0 -1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_222

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c+1, d+1, e, f⟩
  | ⟨a, b+1, c, d, e+2, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+1, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- Phase 1: R3/R1 loop consuming f
-- (0, 1, C+2*k, D+k, 0, F-k) ->* (0, 1, C+2*F, D+F, 0, 0)
-- but parameterized as: starting from (0, 1, 0, D, 0, F)
theorem r3r1_loop : ∀ k : ℕ, ∀ C D,
    ⟨0, 1, C, D, 0, k⟩ [fm]⊢* ⟨0, 1, C + 2 * k, D + k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro C D; exists 0
  | succ k ih =>
    intro C D
    step fm; step fm
    apply stepStar_trans (ih (C + 2) (D + 1))
    ring_nf; finish

-- Phase 2: 5-step transition
-- (0, 1, C, D, 0, 0) -> (0, 0, C, D+1, 0, 1) when C >= 1
theorem transition (C D : ℕ) :
    ⟨0, 1, C + 1, D, 0, 0⟩ [fm]⊢* ⟨0, 0, C + 1, D + 1, 0, 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Phase 3: R4 drain
-- (0, 0, C, D, E, F) ->* (0, 0, 0, D, E+C, F+C)
theorem r4_drain : ∀ C : ℕ, ∀ D E F,
    ⟨0, 0, C, D, E, F⟩ [fm]⊢* ⟨0, 0, 0, D, E + C, F + C⟩ := by
  intro C; induction C with
  | zero => intro D E F; exists 0
  | succ C ih =>
    intro D E F
    step fm
    apply stepStar_trans (ih D (E + 1) (F + 1))
    ring_nf; finish

-- Phase 4: R5+R2 drain pairs
-- (0, 0, 0, D+k, 3*k+1, F) ->* (0, 0, 0, D, 1, F)
theorem r5r2_drain : ∀ k : ℕ, ∀ D F,
    ⟨0, 0, 0, D + k, 3 * k + 1, F⟩ [fm]⊢* ⟨0, 0, 0, D, 1, F⟩ := by
  intro k; induction k with
  | zero => intro D F; exists 0
  | succ k ih =>
    intro D F
    rw [show D + (k + 1) = (D + k) + 1 from by ring,
        show 3 * (k + 1) + 1 = (3 * k + 1) + 3 from by ring]
    step fm; step fm
    apply stepStar_trans (ih D F)
    finish

-- Full cycle: (0, 1, 0, D+1, 0, 3*(D+1)-1) ->+ (0, 1, 0, 2*(D+1), 0, 3*(2*(D+1))-1)
-- i.e., (0, 1, 0, D+1, 0, 3*D+2) ->+ (0, 1, 0, 2*D+2, 0, 6*D+5)
theorem full_cycle (D : ℕ) :
    ⟨0, 1, 0, D + 1, 0, 3 * D + 2⟩ [fm]⊢⁺ ⟨0, 1, 0, 2 * D + 2, 0, 6 * D + 5⟩ := by
  -- Phase 1: r3r1_loop with k = 3*D+2
  apply stepStar_stepPlus_stepPlus (r3r1_loop (3 * D + 2) 0 (D + 1))
  simp only [Nat.zero_add]
  -- Now at (0, 1, 2*(3*D+2), D+1+3*D+2, 0, 0) = (0, 1, 6*D+4, 4*D+3, 0, 0)
  -- Phase 2: transition (need C+1 = 6*D+4, so C = 6*D+3)
  rw [show 2 * (3 * D + 2) = (6 * D + 3) + 1 from by ring,
      show D + 1 + (3 * D + 2) = 4 * D + 3 from by ring]
  apply stepStar_stepPlus_stepPlus (transition (6 * D + 3) (4 * D + 3))
  -- Now at (0, 0, 6*D+4, 4*D+4, 0, 1)
  rw [show (6 * D + 3) + 1 = 6 * D + 4 from by ring,
      show 4 * D + 3 + 1 = 4 * D + 4 from by ring]
  -- Phase 3: r4_drain with C = 6*D+4
  apply stepStar_stepPlus_stepPlus (r4_drain (6 * D + 4) (4 * D + 4) 0 1)
  simp only [Nat.zero_add]
  -- Now at (0, 0, 0, 4*D+4, 6*D+4, 6*D+5)
  rw [show 1 + (6 * D + 4) = 6 * D + 5 from by ring]
  -- Phase 4: r5r2_drain with k = 2*D+1
  -- Need: 4*D+4 = (2*D+2) + (2*D+1) + 1 and 6*D+4 = 3*(2*D+1)+1
  rw [show 4 * D + 4 = (2 * D + 2) + 1 + (2 * D + 1) from by ring,
      show 6 * D + 4 = 3 * (2 * D + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r5r2_drain (2 * D + 1) ((2 * D + 2) + 1) (6 * D + 5))
  -- Now at (0, 0, 0, 2*D+3, 1, 6*D+5)
  -- Final R5: need d >= 1 and e >= 1
  rw [show (2 * D + 2) + 1 = (2 * D + 2) + 1 from by ring]
  step fm
  -- Now at (0, 1, 0, 2*D+2, 0, 6*D+5)
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 1, 0, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun D ↦ ⟨0, 1, 0, D + 1, 0, 3 * D + 2⟩) 0
  intro D; exact ⟨2 * D + 1, by
    show ⟨0, 1, 0, D + 1, 0, 3 * D + 2⟩ [fm]⊢⁺ ⟨0, 1, 0, (2 * D + 1) + 1, 0, 3 * (2 * D + 1) + 2⟩
    rw [show (2 * D + 1) + 1 = 2 * D + 2 from by ring,
        show 3 * (2 * D + 1) + 2 = 6 * D + 5 from by ring]
    exact full_cycle D⟩

end Sz22_2003_unofficial_222
