import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #578: [35/6, 11/2, 4/55, 3/7, 490/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 1  0  1  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_578

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d+2, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R3R2R2 drain: convert c to e (requires e >= 1)
theorem r3r2r2_drain : ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1⟩ := by
  have many_step : ∀ k c e, ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1⟩ := by
    intro k; induction' k with k h <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c e

-- R3R1R1 chain: each round decreases b by 2, increases c by 1, d by 2, decreases e by 1
theorem r3r1r1_chain : ⟨0, b+2*k+1, c+1, d, e+k+1⟩ [fm]⊢* ⟨0, b+1, c+k+1, d+2*k, e+1⟩ := by
  have many_step : ∀ k b c d e, ⟨0, b+2*k+1, c+1, d, e+k+1⟩ [fm]⊢* ⟨0, b+1, c+k+1, d+2*k, e+1⟩ := by
    intro k; induction' k with k h <;> intro b c d e
    · exists 0
    rw [show b + 2 * (k + 1) + 1 = (b + 2 * k + 1) + 2 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _ _)
    ring_nf; finish
  exact many_step k b c d e

-- Last round when b=1: R3, R1, R2
theorem last_round : ⟨0, 1, c+1, d, e+1⟩ [fm]⊢* ⟨0, 0, c+1, d+1, e+1⟩ := by
  step fm; step fm; step fm; finish

-- Compose phases into the full transition
theorem phases_combined : ⟨0, 2*n+1, 2, 3, n+1⟩ [fm]⊢* ⟨0, 0, n+2, 2*n+4, 1⟩ := by
  -- R3R1R1 chain: (0, 2*n+1, 2, 3, n+1) ->* (0, 1, n+2, 2*n+3, 1)
  rw [show (2 : ℕ)*n+1 = 0 + 2*n + 1 from by ring,
      show (2 : ℕ) = 0 + 1 + 1 from by ring,
      show (n : ℕ) + 1 = 0 + n + 1 from by ring]
  apply stepStar_trans r3r1r1_chain
  -- Last round: (0, 1, n+2, 2*n+3, 1) ->* (0, 0, n+2, 2*n+4, 1)
  rw [show (1 : ℕ) + n + 1 = (n + 1) + 1 from by ring,
      show (3 : ℕ) + 2 * n = (2 * n + 3) from by ring,
      show (0 : ℕ) + 1 = 0 + 1 from by ring]
  apply stepStar_trans last_round
  ring_nf; finish

-- Main transition: (0, 0, 0, 2*(n+1), n+2) ->+ (0, 0, 0, 2*(n+2), n+3)
theorem main_trans : ⟨0, 0, 0, 2*(n+1), n+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*(n+2), n+3⟩ := by
  -- Phase 1: R4 drain: ->* (0, 2*(n+1), 0, 0, n+2)
  rw [show 2*(n+1) = 0 + 2*(n+1) from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  simp only [Nat.zero_add]
  -- Phase 2: R5: (0, 2*(n+1), 0, 0, n+2) ->⁺ ...
  rw [show (n : ℕ) + 2 = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Phase 3: R1: (1, 2*(n+1), 1, 2, n+1) ->* ...
  rw [show 2*(n+1) = (2*n+1) + 1 from by ring]
  apply stepStar_trans (step_stepStar (by unfold fm; rfl))
  -- Phase 4+5: combined phases ->* (0, 0, n+2, 2*n+4, 1)
  apply stepStar_trans phases_combined
  -- Phase 6: R3R2R2 drain: (0, 0, n+2, 2*n+4, 1) ->* (0, 0, 0, 2*n+4, n+3)
  rw [show n + 2 = 0 + (n + 2) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans r3r2r2_drain
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2*(n+1), n+2⟩) 0
  intro n; exact ⟨n+1, main_trans⟩

end Sz22_2003_unofficial_578
