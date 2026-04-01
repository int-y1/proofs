import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1526: [7/30, 121/2, 6/77, 25/11, 14/5]

Vector representation:
```
-1 -1 -1  1  0
-1  0  0  0  2
 1  1  0 -1 -1
 0  0  2  0 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1526

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R3/R2 alternating chain.
theorem r3r2_chain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b, 0, d + k, e + 1⟩ [fm]⊢* ⟨0, b + k, 0, d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) d (e + 1)); ring_nf; finish

-- R4 chain: drain e to c.
theorem r4_chain : ∀ k, ∀ b c,
    ⟨(0 : ℕ), b, c, 0, k⟩ [fm]⊢* ⟨0, b, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih b (c + 2)); ring_nf; finish

-- Combined R5/R1 drain + tail.
-- From (0, k, 2k+4, D, 0) to (1, 0, 0, D+2k+2, 0).
-- k+1 case: R5,R1 then recurse. k=0 case: 7 explicit steps using simp [fm].
theorem drain_and_tail : ∀ k, ∀ D,
    ⟨(0 : ℕ), k, 2 * k + 4, D, 0⟩ [fm]⊢* ⟨1, 0, 0, D + 2 * k + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro D
  · -- k=0: (0,0,4,D,0) → (1,0,0,D+2,0) in 7 steps.
    -- R5: (0,0,4,D,0) → (1,0,3,D+1,0)
    apply stepStar_trans (step_stepStar
      (show (⟨(0 : ℕ), 0, 4, D, 0⟩ : Q) [fm]⊢ ⟨1, 0, 3, D + 1, 0⟩ from by simp [fm]))
    -- R2: (1,0,3,D+1,0) → (0,0,3,D+1,2)
    apply stepStar_trans (step_stepStar
      (show (⟨1, (0 : ℕ), 3, D + 1, 0⟩ : Q) [fm]⊢ ⟨0, 0, 3, D + 1, 2⟩ from by simp [fm]))
    -- R3: (0,0,3,D+1,2) → (1,1,3,D,1). Need D+1 = D+1 form.
    rw [show D + 1 = D + 1 from rfl, show (2 : ℕ) = 1 + 1 from rfl]
    step fm
    -- R1: (1,1,3,D,1) → (0,0,2,D+1,1)
    step fm
    -- R3: (0,0,2,D+1,1) → (1,1,2,D,0)
    rw [show D + 1 = D + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    -- R1: (1,1,2,D,0) → (0,0,1,D+1,0)
    apply stepStar_trans (step_stepStar
      (show (⟨1, 1, 2, D, (0 : ℕ)⟩ : Q) [fm]⊢ ⟨0, 0, 1, D + 1, 0⟩ from by simp [fm]))
    -- R5: (0,0,1,D+1,0) → (1,0,0,D+2,0)
    apply stepStar_trans (step_stepStar
      (show (⟨(0 : ℕ), 0, 1, D + 1, 0⟩ : Q) [fm]⊢ ⟨1, 0, 0, D + 2, 0⟩ from by simp [fm]))
    ring_nf; finish
  · -- k+1: (0,k+1,2k+6,D,0).
    -- R5: (1,k+1,2k+5,D+1,0). R1: (0,k,2k+4,D+2,0).
    rw [show 2 * (k + 1) + 4 = (2 * k + 4) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (D + 2)); ring_nf; finish

-- Main transition: (1, 0, 0, d, 0) ⊢⁺ (1, 0, 0, 2*d+2, 0).
theorem main_trans (d : ℕ) :
    ⟨1, 0, 0, d, (0 : ℕ)⟩ [fm]⊢⁺ ⟨1, 0, 0, 2 * d + 2, 0⟩ := by
  -- R2: (1,0,0,d,0) → (0,0,0,d,2)
  apply step_stepStar_stepPlus
    (show (⟨1, 0, 0, d, (0 : ℕ)⟩ : Q) [fm]⊢ ⟨0, 0, 0, d, 2⟩ from by simp [fm])
  -- R3/R2 chain, d rounds: (0,0,0,d,2) → (0,d,0,0,d+2)
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show (d : ℕ) = 0 + d from by ring]
  apply stepStar_trans (r3r2_chain d 0 0 1)
  rw [show 1 + d + 1 = d + 2 from by ring,
      show 0 + d = d from by ring]
  -- R4 chain, d+2 steps: (0,d,0,0,d+2) → (0,d,2d+4,0,0)
  apply stepStar_trans (r4_chain (d + 2) d 0)
  -- drain_and_tail with k=d, D=0
  rw [show 0 + 2 * (d + 2) = 2 * d + 4 from by ring]
  apply stepStar_trans (drain_and_tail d 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨1, 0, 0, d, 0⟩) 2
  intro d; exact ⟨2 * d + 2, main_trans d⟩

end Sz22_2003_unofficial_1526
