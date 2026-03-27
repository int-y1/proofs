import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #84: [1/30, 12/77, 7/2, 25/7, 242/5]

Vector representation:
```
-1 -1 -1  0  0
 2  1  0 -1 -1
-1  0  0  1  0
 0  0  2 -1  0
 1  0 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_84

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R2/R3 loop: (j, j, 0, 1, e+1) ->* (j+e+2, j+e+1, 0, 0, 0)
theorem r2r3_loop : ∀ e, ∀ j, ⟨j, j, 0, 1, e + 1⟩ [fm]⊢* ⟨j + e + 2, j + e + 1, 0, 0, 0⟩ := by
  intro e; induction' e with e ih <;> intro j
  · step fm; ring_nf; finish
  · step fm; step fm
    apply stepStar_trans (ih (j + 1))
    ring_nf; finish

-- R3 drain: (n, b, 0, d, 0) ->* (0, b, 0, d+n, 0)
theorem r3_drain : ∀ n, ∀ b d, ⟨n, b, 0, d, 0⟩ [fm]⊢* ⟨0, b, 0, d + n, 0⟩ := by
  intro n; induction' n with n ih <;> intro b d
  · exists 0
  step fm
  apply stepStar_trans (ih b (d + 1))
  ring_nf; finish

-- R4 drain: (0, b, c, k, 0) ->* (0, b, c+2*k, 0, 0)
theorem r4_drain : ∀ k, ∀ b c, ⟨0, b, c, k, 0⟩ [fm]⊢* ⟨0, b, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  step fm
  apply stepStar_trans (ih b (c + 2))
  ring_nf; finish

-- R5/R1 interleave: (0, k, 2*k+2, 0, e) ->* (0, 0, 2, 0, e+2*k)
theorem r5r1_interleave : ∀ k, ∀ e, ⟨0, k, 2 * k + 2, 0, e⟩ [fm]⊢* ⟨0, 0, 2, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih (e + 2))
  ring_nf; finish

-- Full transition as stepStar: (0, 0, 0, 1, e+1) ->* (1, 0, 0, 0, 2*e+3)
theorem full_phase (e : ℕ) : ⟨0, 0, 0, 1, e + 1⟩ [fm]⊢* ⟨1, 0, 0, 0, 2 * e + 3⟩ := by
  -- R2/R3 loop: (0, 0, 0, 1, e+1) ->* (e+2, e+1, 0, 0, 0)
  apply stepStar_trans (r2r3_loop e 0)
  simp only [Nat.zero_add]
  -- R3 drain: (e+2, e+1, 0, 0, 0) ->* (0, e+1, 0, e+2, 0)
  apply stepStar_trans (r3_drain (e + 2) (e + 1) 0)
  simp only [Nat.zero_add]
  -- R4 drain: (0, e+1, 0, e+2, 0) ->* (0, e+1, 2*(e+2), 0, 0)
  apply stepStar_trans (r4_drain (e + 2) (e + 1) 0)
  simp only [Nat.zero_add]
  -- R5/R1 interleave: rewrite 2*(e+2) = 2*(e+1)+2
  rw [show 2 * (e + 2) = 2 * (e + 1) + 2 from by ring]
  apply stepStar_trans (r5r1_interleave (e + 1) 0)
  simp only [Nat.zero_add]
  -- Final 4 steps: R5, R3, R2, R1
  step fm; step fm; step fm; step fm
  rw [show 2 * (e + 1) + 1 = 2 * e + 3 from by ring]
  finish

-- Main transition: (1, 0, 0, 0, e+1) ->+ (1, 0, 0, 0, 2*e+3)
theorem main_trans (e : ℕ) : ⟨1, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2 * e + 3⟩ := by
  -- R3: (1, 0, 0, 0, e+1) -> (0, 0, 0, 1, e+1)
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  exact full_phase e

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨1, 0, 0, 0, e + 1⟩) 0
  intro e; exact ⟨2 * e + 2, main_trans e⟩

end Sz22_2003_unofficial_84
