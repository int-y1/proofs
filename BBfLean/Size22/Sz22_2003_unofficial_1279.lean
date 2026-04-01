import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1279: [56/15, 18/7, 1/6, 25/2, 7/5]

Vector representation:
```
 3 -1 -1  1
 1  2  0 -1
-1 -1  0  0
-1  0  2  0
 0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1279

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+3, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

-- R4 chain: (a + k, 0, c, 0) -> (a, 0, c + 2*k, 0)
theorem r4_chain : ∀ k a c, ⟨a + k, (0 : ℕ), c, (0 : ℕ)⟩ [fm]⊢* ⟨a, (0 : ℕ), c + 2 * k, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2))
    rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring]
    finish

-- R2 chain (with c = 0): (a, b, 0, d + k) -> (a + k, b + 2*k, 0, d)
theorem r2_chain : ∀ k a b d, ⟨a, b, (0 : ℕ), d + k⟩ [fm]⊢* ⟨a + k, b + 2 * k, (0 : ℕ), d⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) (b + 2) d)
    rw [show a + 1 + k = a + (k + 1) from by ring,
        show b + 2 + 2 * k = b + 2 * (k + 1) from by ring]
    finish

-- R3 chain: (a + k, b + k, 0, 0) -> (a, b, 0, 0)
theorem r3_chain : ∀ k a b, ⟨a + k, b + k, (0 : ℕ), (0 : ℕ)⟩ [fm]⊢* ⟨a, b, (0 : ℕ), (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    exact ih a b

-- Interleaved R2,R1,R1 chain: k rounds
-- Each round: (a_v, 0, c+1+2k, d+1) -> R2 -> R1 -> R1 -> (a_v+7, 0, c+1+2(k-1), d+2)
theorem r2r1r1_chain : ∀ k a c d,
    ⟨a, (0 : ℕ), c + 1 + 2 * k, d + 1⟩ [fm]⊢* ⟨a + 7 * k, (0 : ℕ), c + 1, d + 1 + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · -- Do one round of R2, R1, R1, then apply IH
    rw [show c + 1 + 2 * (k + 1) = (c + 2 * k + 2) + 1 from by ring,
        show d + 1 = (d) + 1 from by ring]
    step fm  -- R2: (a+1, 2, (c+2k+2)+1, d)
    rw [show (c + 2 * k + 2) + 1 = (c + 2 * k + 1) + 1 + 1 from by ring,
        show d = (d) from rfl]
    step fm  -- R1: (a+4, 1, (c+2k+1)+1, d+1)
    rw [show (c + 2 * k + 1) + 1 = (c + 2 * k) + 1 + 1 from by ring]
    step fm  -- R1: (a+7, 0, (c+2k)+1, d+2)
    rw [show (c + 2 * k) + 1 = c + 1 + 2 * k from by ring,
        show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 7) c (d + 1))
    rw [show a + 7 + 7 * k = a + 7 * (k + 1) from by ring,
        show d + 1 + 1 + k = d + 1 + (k + 1) from by ring]
    finish

-- Main transition: (a + 2, 0, 0, 0) ->+ (6*a + 8, 0, 0, 0)
theorem main_transition (a : ℕ) :
    ⟨a + 2, (0 : ℕ), 0, (0 : ℕ)⟩ [fm]⊢⁺ ⟨6 * a + 8, (0 : ℕ), 0, (0 : ℕ)⟩ := by
  -- Phase 1: R4 x (a+2): (a+2, 0, 0, 0) -> (0, 0, 2a+4, 0)
  rw [show a + 2 = 0 + (a + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (a + 2) 0 0)
  rw [show (0 : ℕ) + 2 * (a + 2) = 2 * a + 4 from by ring]
  -- State: (0, 0, 2a+4, 0)
  -- Phase 2: R5: (0, 0, 2a+4, 0) -> (0, 0, 2a+3, 1)
  rw [show 2 * a + 4 = (2 * a + 3) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0, (2 * a + 3) + 1, 0⟩ : Q) [fm]⊢ ⟨0, 0, 2 * a + 3, 1⟩)
  -- State: (0, 0, 2a+3, 1)
  -- Phase 3: R2: (0, 0, 2a+3, 1) -> (1, 2, 2a+3, 0)
  apply stepStar_trans
    (step_stepStar (by simp [fm] : (⟨0, 0, 2 * a + 3, 1⟩ : Q) [fm]⊢ ⟨1, 2, 2 * a + 3, 0⟩))
  -- State: (1, 2, 2a+3, 0)
  -- Phase 4: R1, R1: (1, 2, 2a+3, 0) -> (7, 0, 2a+1, 2)
  rw [show 2 * a + 3 = (2 * a + 1) + 1 + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans
    (step_stepStar (by simp [fm] : (⟨1, 1 + 1, (2 * a + 1) + 1 + 1, 0⟩ : Q) [fm]⊢ ⟨4, 1, (2 * a + 1) + 1, 1⟩))
  rw [show (2 * a + 1) + 1 = (2 * a) + 1 + 1 from by ring]
  apply stepStar_trans
    (step_stepStar (by simp [fm] : (⟨4, 1, (2 * a) + 1 + 1, 1⟩ : Q) [fm]⊢ ⟨7, 0, (2 * a) + 1, 2⟩))
  -- State: (7, 0, 2a+1, 2)
  -- Phase 5: R2,R1,R1 x a rounds: (7, 0, 2a+1, 2) -> (7+7a, 0, 1, a+2)
  rw [show (2 * a) + 1 = 0 + 1 + 2 * a from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r2r1r1_chain a 7 0 1)
  rw [show 7 + 7 * a = 7 * a + 7 from by ring,
      show (0 : ℕ) + 1 = 1 from by ring,
      show 1 + 1 + a = a + 2 from by ring]
  -- State: (7a+7, 0, 1, a+2)
  -- Phase 6: R2: (7a+7, 0, 1, a+2) -> (7a+8, 2, 1, a+1)
  rw [show a + 2 = (a + 1) + 1 from by ring]
  apply stepStar_trans
    (step_stepStar (by simp [fm] : (⟨7 * a + 7, 0, 1, (a + 1) + 1⟩ : Q) [fm]⊢ ⟨7 * a + 8, 2, 1, a + 1⟩))
  -- R1: (7a+8, 2, 1, a+1) -> (7a+11, 1, 0, a+2)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans
    (step_stepStar (by simp [fm] : (⟨7 * a + 8, 1 + 1, 0 + 1, a + 1⟩ : Q) [fm]⊢ ⟨7 * a + 11, 1, 0, a + 2⟩))
  -- State: (7a+11, 1, 0, a+2)
  -- Phase 7: R2 x (a+2): (7a+11, 1, 0, a+2) -> (8a+13, 2a+5, 0, 0)
  rw [show a + 2 = 0 + (a + 2) from by ring]
  apply stepStar_trans (r2_chain (a + 2) (7 * a + 11) 1 0)
  rw [show 7 * a + 11 + (a + 2) = 8 * a + 13 from by ring,
      show 1 + 2 * (a + 2) = 2 * a + 5 from by ring]
  -- State: (8a+13, 2a+5, 0, 0)
  -- Phase 8: R3 x (2a+5): (8a+13, 2a+5, 0, 0) -> (6a+8, 0, 0, 0)
  have h := r3_chain (2 * a + 5) (6 * a + 8) 0
  rw [show 6 * a + 8 + (2 * a + 5) = 8 * a + 13 from by ring,
      show (0 : ℕ) + (2 * a + 5) = 2 * a + 5 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun a ↦ ⟨a + 2, 0, 0, 0⟩) 0
  intro a; exists 6 * a + 6
  have h := main_transition a
  rw [show 6 * a + 6 + 2 = 6 * a + 8 from by ring]
  exact h

end Sz22_2003_unofficial_1279
