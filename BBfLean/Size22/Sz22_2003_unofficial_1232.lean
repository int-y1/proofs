import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1232: [5/6, 5929/2, 44/35, 3/11, 5/3]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  2
 2  0 -1 -1  1
 0  1  0  0 -1
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1232

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move e to b. (0, b, 0, d, e+k) ->* (0, b+k, 0, d, e)
theorem e_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- Interleaved chain: k rounds of (R3, R1, R1).
-- (0, b+2k, c+1, d+k, e) ->* (0, b, c+k+1, d, e+k)
theorem interleaved : ∀ k, ∀ b c d e, ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro b c d e; simp; exists 0
  · intro b c d e
    rw [show b + 2 * (k + 1) = b + 2 * k + 2 from by ring,
        show c + 1 = c + 1 from rfl,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    rw [show c + 1 + k + 1 = c + (k + 1) + 1 from by ring,
        show e + 1 + k = e + (k + 1) from by ring]
    finish

-- R3R2R2 chain: k rounds, each c-=1, d+=3, e+=5.
-- (0, 0, c+k, d+1, e) ->* (0, 0, c, d+3k+1, e+5k)
theorem r3r2r2_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + 3 * k + 1, e + 5 * k⟩ := by
  intro k; induction' k with k ih
  · intro c d e; simp; exists 0
  · intro c d e
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e)
    rw [show d + 3 * k + 1 = (d + 3 * k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 3 * k + 4 = d + 3 * (k + 1) + 1 from by ring,
        show e + 5 * k + 5 = e + 5 * (k + 1) from by ring]
    finish

-- Main transition: (0, 0, 0, d+k+2, 2k+2) ->+ (0, 0, 0, d+3k+6, 6k+8)
-- = (0, 0, 0, (d+1)+(3k+3)+2, 2*(3k+3)+2)
theorem main_trans (d k : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, d + k + 2, 2 * k + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, d + 3 * k + 6, 6 * k + 8⟩ := by
  -- Phase 1: R4 x (2k+2): e -> b
  rw [show (2 * k + 2 : ℕ) = 0 + (2 * k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * k + 2) 0 (d + k + 2) 0)
  rw [show (0 : ℕ) + (2 * k + 2) = 2 * k + 2 from by ring]
  -- State: (0, 2k+2, 0, d+k+2, 0)
  -- Phase 2: R5
  rw [show (2 * k + 2 : ℕ) = (2 * k + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (by simp [fm] : (⟨0, (2 * k + 1) + 1, 0, d + k + 2, 0⟩ : Q) [fm]⊢ ⟨0, 2 * k + 1, 1, d + k + 2, 0⟩)
  -- State: (0, 2k+1, 1, d+k+2, 0)
  -- Phase 3: interleaved chain with k rounds
  rw [show (2 * k + 1 : ℕ) = 1 + 2 * k from by ring,
      show d + k + 2 = (d + 2) + k from by ring]
  apply stepStar_trans (interleaved k 1 0 (d + 2) 0)
  rw [show (0 : ℕ) + k + 1 = k + 1 from by ring,
      show (0 : ℕ) + k = k from by ring]
  -- State: (0, 1, k+1, d+2, k)
  -- Phase 4: R3
  rw [show k + 1 = k + 1 from rfl,
      show d + 2 = (d + 1) + 1 from by ring]
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 1, k + 1, (d + 1) + 1, k⟩ : Q) [fm]⊢ ⟨2, 1, k, d + 1, k + 1⟩))
  -- State: (2, 1, k, d+1, k+1)
  -- Phase 5: R1
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨2, 1, k, d + 1, k + 1⟩ : Q) [fm]⊢ ⟨1, 0, k + 1, d + 1, k + 1⟩))
  -- State: (1, 0, k+1, d+1, k+1)
  -- Phase 6: R2
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨1, 0, k + 1, d + 1, k + 1⟩ : Q) [fm]⊢ ⟨0, 0, k + 1, d + 3, k + 3⟩))
  -- State: (0, 0, k+1, d+3, k+3)
  -- Phase 7: R3R2R2 chain with k+1 rounds
  rw [show k + 1 = 0 + (k + 1) from by ring,
      show d + 3 = (d + 2) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (k + 1) 0 (d + 2) (k + 3))
  rw [show d + 2 + 3 * (k + 1) + 1 = d + 3 * k + 6 from by ring,
      show k + 3 + 5 * (k + 1) = 6 * k + 8 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, k⟩ ↦ ⟨0, 0, 0, d + k + 2, 2 * k + 2⟩) ⟨0, 0⟩
  intro ⟨d, k⟩
  exists ⟨d + 1, 3 * k + 3⟩
  show ⟨(0 : ℕ), (0 : ℕ), 0, d + k + 2, 2 * k + 2⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), 0, (d + 1) + (3 * k + 3) + 2, 2 * (3 * k + 3) + 2⟩
  have h := main_trans d k
  rw [show (d + 1) + (3 * k + 3) + 2 = d + 3 * k + 6 from by ring,
      show 2 * (3 * k + 3) + 2 = 6 * k + 8 from by ring]
  exact h

end Sz22_2003_unofficial_1232
