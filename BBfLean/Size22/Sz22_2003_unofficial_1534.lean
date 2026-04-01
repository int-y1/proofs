import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1534: [7/30, 22/3, 27/77, 5/11, 9/2]

Vector representation:
```
-1 -1 -1  1  0
 1 -1  0  0  1
 0  3  0 -1 -1
 0  0  1  0 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1534

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R3,R2,R2,R2 chain: each step decrements d and increments a by 3 and e by 2
theorem inner_loop : ∀ k, ∀ a d e, ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, d, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) d (e + 2))
    ring_nf; finish

-- R4 chain: each step moves one from e to c
theorem e_to_c : ∀ k, ∀ a c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · ring_nf; exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

-- R5,R1,R1 chain: each cycle decrements a by 3 and c by 2, increments d by 2
theorem drain_ac : ∀ k, ∀ a c D, ⟨a + 3 * k, 0, c + 2 * k, D, 0⟩ [fm]⊢* ⟨a, 0, c, D + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c D
  · ring_nf; exists 0
  · rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (D + 2))
    ring_nf; finish

-- Endgame: (2, 0, 2, D, 0) ->+ (2, 0, 0, D+1, 2)
theorem endgame : ⟨2, 0, 2, D, 0⟩ [fm]⊢⁺ ⟨2, 0, 0, D + 1, 2⟩ := by
  execute fm 7

-- Main transition: (2, 0, 0, d, 2) ->+ (2, 0, 0, 2*d+1, 2)
theorem main_trans : ⟨2, 0, 0, d, 2⟩ [fm]⊢⁺ ⟨2, 0, 0, 2 * d + 1, 2⟩ := by
  -- Phase 1: inner_loop d times
  apply stepStar_stepPlus_stepPlus
  · rw [show (d : ℕ) = 0 + d from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    have := inner_loop d 2 0 1
    rw [show (0 : ℕ) + d = d from by ring,
        show 2 + 3 * d = 3 * d + 2 from by ring,
        show 1 + 2 * d + 1 = 2 * d + 2 from by ring] at this
    rw [show (0 : ℕ) + d = d from by ring]
    exact this
  -- Phase 2: e_to_c
  apply stepStar_stepPlus_stepPlus
  · have := e_to_c (2 * d + 2) (3 * d + 2) 0
    rw [show 0 + (2 * d + 2) = 2 * d + 2 from by ring] at this
    exact this
  -- Phase 3: drain_ac
  apply stepStar_stepPlus_stepPlus
  · have := drain_ac d 2 2 0
    rw [show 2 + 3 * d = 3 * d + 2 from by ring,
        show 2 + 2 * d = 2 * d + 2 from by ring,
        show 0 + 2 * d = 2 * d from by ring] at this
    exact this
  -- Phase 4: endgame
  exact endgame

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨2, 0, 0, d, 2⟩) 0
  intro d; exists 2 * d + 1; exact main_trans
