import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1211: [5/6, 539/2, 4/385, 3/11, 55/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1 -1
 0  1  0  0 -1
 0  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1211

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 repeated: move e to b
theorem e_to_b : ∀ k b d, ⟨(0 : ℕ), b, 0, d, k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro b d; exists 0
  · intro b d
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- One round: (0, b+2, c, d+1+1, 0) -> (0, b, c+2, d, 0) via R5-R3-R1-R1
theorem r5r3r1r1_one : ∀ b c d,
    ⟨(0 : ℕ), b + 2, c, d + 1 + 1, (0 : ℕ)⟩ [fm]⊢*
    ⟨(0 : ℕ), b, c + 2, d, (0 : ℕ)⟩ := by
  intro b c d
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, b + 2, c, d + 1 + 1, 0⟩ : Q) [fm]⊢ ⟨0, b + 2, c + 1, d + 1, 1⟩))
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, b + 2, c + 1, d + 1, 1⟩ : Q) [fm]⊢ ⟨2, b + 2, c, d, 0⟩))
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨2, b + 2, c, d, 0⟩ : Q) [fm]⊢ ⟨1, b + 1, c + 1, d, 0⟩))
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, b + 1, c + 1, d, 0⟩ : Q) [fm]⊢ ⟨0, b, c + 2, d, 0⟩))
  finish

-- Chain k rounds
theorem r5r3r1r1_chain : ∀ k, ∀ b c d,
    ⟨(0 : ℕ), b + 2 * k, c, d + 2 * k, (0 : ℕ)⟩ [fm]⊢*
    ⟨(0 : ℕ), b, c + 2 * k, d, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih
  · intro b c d; simp; exists 0
  · intro b c d
    rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 2))
    rw [show d + 2 = d + 1 + 1 from by ring]
    apply stepStar_trans (r5r3r1r1_one b (c + 2 * k) d)
    rw [show c + 2 * k + 2 = c + 2 * (k + 1) from by ring]
    finish

-- R2-R2-R3 chain
theorem r2r2r3_chain : ∀ k, ∀ c d e,
    ⟨(2 : ℕ), (0 : ℕ), c + k, d, e⟩ [fm]⊢*
    ⟨(2 : ℕ), (0 : ℕ), c, d + 3 * k, e + k⟩ := by
  intro k; induction' k with k ih
  · intro c d e; simp; exists 0
  · intro c d e
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e)
    step fm
    step fm
    rw [show d + 3 * k + 4 = (d + 3 * k + 3) + 1 from by ring,
        show e + k + 2 = (e + k + 1) + 1 from by ring]
    step fm
    rw [show d + 3 * k + 3 = d + 3 * (k + 1) from by ring,
        show e + k + 1 = e + (k + 1) from by ring]
    finish

-- Main transition: (0, 0, 0, 2k^2+4k+5, 2k+2) ->+ (0, 0, 0, 2k^2+8k+11, 2k+4)
theorem main_transition (k : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, 2 * k * k + 4 * k + 5, 2 * k + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 2 * k * k + 8 * k + 11, 2 * k + 4⟩ := by
  -- Phase 1: e_to_b
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * k + 2) 0 (2 * k * k + 4 * k + 5))
  rw [show (0 : ℕ) + (2 * k + 2) = 2 * k + 2 from by ring]
  -- State: (0, 2k+2, 0, 2k^2+4k+5, 0)
  -- Phase 2: r5r3r1r1_chain, k+1 rounds
  rw [show 2 * k + 2 = 0 + 2 * (k + 1) from by ring,
      show 2 * k * k + 4 * k + 5 = (2 * k * k + 2 * k + 3) + 2 * (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r3r1r1_chain (k + 1) 0 0 (2 * k * k + 2 * k + 3))
  rw [show 0 + 2 * (k + 1) = 2 * k + 2 from by ring]
  -- State: (0, 0, 2k+2, 2k^2+2k+3, 0)
  -- Phase 3: R5
  rw [show 2 * k * k + 2 * k + 3 = (2 * k * k + 2 * k + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0, 2 * k + 2, (2 * k * k + 2 * k + 2) + 1, 0⟩ : Q) [fm]⊢
      ⟨0, 0, 2 * k + 2 + 1, 2 * k * k + 2 * k + 2, 1⟩)
  -- State: (0, 0, 2k+3, 2k^2+2k+2, 1)
  -- R3
  rw [show 2 * k + 2 + 1 = (2 * k + 2) + 1 from by ring,
      show 2 * k * k + 2 * k + 2 = (2 * k * k + 2 * k + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, 0, (2 * k + 2) + 1, (2 * k * k + 2 * k + 1) + 1, 0 + 1⟩ : Q) [fm]⊢
      ⟨2, 0, 2 * k + 2, 2 * k * k + 2 * k + 1, 0⟩))
  -- State: (2, 0, 2k+2, 2k^2+2k+1, 0)
  -- Phase 4: r2r2r3_chain, 2k+2 rounds
  rw [show 2 * k + 2 = 0 + (2 * k + 2) from by ring]
  apply stepStar_trans (r2r2r3_chain (2 * k + 2) 0 (2 * k * k + 2 * k + 1) 0)
  rw [show 2 * k * k + 2 * k + 1 + 3 * (2 * k + 2) = 2 * k * k + 8 * k + 7 from by ring,
      show 0 + (2 * k + 2) = 2 * k + 2 from by ring]
  -- State: (2, 0, 0, 2k^2+8k+7, 2k+2)
  -- Phase 5: two R2 steps
  step fm
  step fm
  rw [show 2 * k * k + 8 * k + 7 + 2 + 2 = 2 * k * k + 8 * k + 11 from by ring,
      show 2 * k + 2 + 1 + 1 = 2 * k + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 2⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n * n + 4 * n + 5, 2 * n + 2⟩) 0
  intro n
  exists n + 1
  show ⟨(0 : ℕ), (0 : ℕ), 0, 2 * n * n + 4 * n + 5, 2 * n + 2⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), 0, 2 * (n + 1) * (n + 1) + 4 * (n + 1) + 5, 2 * (n + 1) + 2⟩
  have h := main_transition n
  rw [show 2 * n * n + 8 * n + 11 = 2 * (n + 1) * (n + 1) + 4 * (n + 1) + 5 from by ring] at h
  rw [show 2 * n + 4 = 2 * (n + 1) + 2 from by ring] at h
  exact h

end Sz22_2003_unofficial_1211
