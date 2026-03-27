import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #353: [2/15, 1/98, 429/2, 175/11, 2/91]

Vector representation:
```
 1 -1 -1  0  0  0
-1  0  0 -2  0  0
-1  1  0  0  1  1
 0  0  2  1 -1  0
 1  0  0 -1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_353

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+2, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+2, d+1, e, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- R3/R1 alternation: each pair decrements c and increments e,f
theorem r3r1_chain : ∀ k c e f,
    ⟨1, 0, c+k, 0, e, f⟩ [fm]⊢* ⟨(1 : ℕ), 0, c, 0, e+k, f+k⟩ := by
  intro k; induction k with
  | zero => intro c e f; exists 0
  | succ k ih =>
    intro c e f
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R4 repeated: each step converts one e into c+2 and d+1
theorem r4_chain : ∀ k c d e f,
    ⟨0, 0, c, d, e+k, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c+2*k, d+k, e, f⟩ := by
  intro k; induction k with
  | zero => intro c d e f; exists 0
  | succ k ih =>
    intro c d e f
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- R5/R2 drain: d=3k+1 with k+1 R5 steps and k R2 steps
theorem r5r2_drain : ∀ k c f,
    ⟨0, 0, c, 3*k+1, 0, f+k+1⟩ [fm]⊢* ⟨(1 : ℕ), 0, c, 0, 0, f⟩ := by
  intro k; induction k with
  | zero => intro c f; step fm; finish
  | succ k ih =>
    intro c f
    rw [show 3 * (k + 1) + 1 = (3 * k + 3) + 1 from by ring,
        show f + (k + 1) + 1 = (f + k + 1) + 1 from by ring]
    step fm
    rw [show 3 * k + 3 = (3 * k + 1) + 2 from by ring]
    step fm
    exact ih c f

-- Middle phase: 9 steps from (1,0,0,0,e,f) to (0,0,1,0,e+1,f+3)
-- R3, R4, R1, R3, R1, R3, R4, R1, R2
theorem middle_phase : ∀ e f,
    ⟨1, 0, 0, 0, e, f⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 1, 0, e+1, f+3⟩ := by
  intro e f
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Full cycle: (1, 0, 3n, 0, 0, 2n) ⊢⁺ (1, 0, 3(2n+1), 0, 0, 2(2n+1))
theorem cycle (n : ℕ) :
    ⟨1, 0, 3*n, 0, 0, 2*n⟩ [fm]⊢⁺ ⟨(1 : ℕ), 0, 3*(2*n+1), 0, 0, 2*(2*n+1)⟩ := by
  -- Phase A: R3/R1 x 3n: (1,0,3n,0,0,2n) ⊢* (1,0,0,0,3n,5n)
  apply stepStar_stepPlus_stepPlus
  · have h := r3r1_chain (3*n) 0 0 (2*n)
    simp only [Nat.zero_add] at h
    rw [show 2 * n + 3 * n = 5 * n from by ring] at h
    exact h
  -- Middle phase: 9 steps: (1,0,0,0,3n,5n) ⊢⁺ (0,0,1,0,3n+1,5n+3)
  apply stepPlus_stepStar_stepPlus (middle_phase (3*n) (5*n))
  -- Phases D+E combined
  -- Goal: (0,0,1,0,3n+1,5n+3) ⊢* (1,0,3(2n+1),0,0,2(2n+1))
  -- = (0,0,1,0,3n+1,5n+3) ⊢* (1,0,6n+3,0,0,4n+2)
  -- Phase D: R4 x (3n+1) then Phase E: R5/R2 drain
  have hD := r4_chain (3*n+1) 1 0 0 (5*n+3)
  simp only [Nat.zero_add] at hD
  have hE := r5r2_drain n (1+2*(3*n+1)) (4*n+2)
  rw [show 4 * n + 2 + n + 1 = 5 * n + 3 from by ring] at hE
  have hDE := stepStar_trans hD hE
  rw [show 1 + 2 * (3 * n + 1) = 6 * n + 3 from by ring] at hDE
  rw [show 3 * (2 * n + 1) = 6 * n + 3 from by ring,
      show 2 * (2 * n + 1) = 4 * n + 2 from by ring]
  exact hDE

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n => ⟨1, 0, 3*n, 0, 0, 2*n⟩) 0
  intro n
  exact ⟨2*n+1, cycle n⟩

end Sz22_2003_unofficial_353
