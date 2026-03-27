import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #192: [1/6, 22/35, 715/2, 21/11, 4/39]

Vector representation:
```
-1 -1  0  0  0  0
 1  0 -1 -1  1  0
-1  0  1  0  1  1
 0  1  0  1 -1  0
 2 -1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_192

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | _ => none

-- R4 drain: move e to b and d
theorem e_drain : ∀ k, ∀ b d f, ⟨0, b, 0, d, k, f⟩ [fm]⊢* ⟨(0 : ℕ), b+k, 0, d+k, 0, f⟩ := by
  intro k; induction k with
  | zero => intro b d f; exists 0
  | succ k ih =>
    intro b d f
    step fm
    apply stepStar_trans (ih (b + 1) (d + 1) f)
    ring_nf; finish

-- R5+R1+R1 drain: each round removes 3 from b and 1 from f
theorem r5r1r1_drain : ∀ k, ∀ b d f, ⟨0, b + 3 * k, 0, d, 0, f + k⟩ [fm]⊢* ⟨(0 : ℕ), b, 0, d, 0, f⟩ := by
  intro k; induction k with
  | zero => intro b d f; simp; exists 0
  | succ k ih =>
    intro b d f
    rw [show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    apply stepStar_trans (ih (b + 3) d (f + 1))
    -- Now prove (0, b+3, 0, d, 0, f+1) →* (0, b, 0, d, 0, f) in 3 steps
    rw [show b + 3 = (b + 2) + 1 from by ring,
        show f + 1 = f + 1 from rfl]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show b + 2 = (b + 1) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show b + 1 = b + 1 from rfl]
    step fm
    finish

-- R3+R2 chain: each round consumes 1 from d, adds 2 to e and 1 to f
theorem r3r2_chain : ∀ k, ∀ d e f, ⟨2, 0, 0, d + k, 2 * e, f⟩ [fm]⊢* ⟨(2 : ℕ), 0, 0, d, 2 * (e + k), f + k⟩ := by
  intro k; induction k with
  | zero => intro d e f; simp; exists 0
  | succ k ih =>
    intro d e f
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
    step fm
    rw [show (d + k) + 1 = (d + k) + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show 2 * e + 1 + 1 = 2 * (e + 1) from by ring]
    apply stepStar_trans (ih d (e + 1) (f + 1))
    ring_nf; finish

-- Consume c=2: (0, 0, 2, 0, e+2, f) →* (0, 0, 0, 0, e+2, f)
theorem c_consume : ∀ e f, ⟨0, 0, 2, 0, e + 2, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, 0, e + 2, f⟩ := by
  intro e f
  rw [show e + 2 = (e + 1) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show e + 1 + 1 = (e + 1) + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  finish

-- Main transition: (0, 3n+1, 0, 3n+1, 0, 2n+1) →⁺ (0, 6n+4, 0, 6n+4, 0, 4n+3)
theorem main_trans (n : ℕ) :
    ⟨0, 3*n+1, 0, 3*n+1, 0, 2*n+1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 6*n+4, 0, 6*n+4, 0, 4*n+3⟩ := by
  -- Phase A: R5+R1+R1 drain n rounds
  -- (0, 3n+1, 0, 3n+1, 0, 2n+1) →* (0, 1, 0, 3n+1, 0, n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 0, 3*n+1, 0, n+1⟩)
  · have h := r5r1r1_drain n 1 (3*n+1) (n+1)
    rw [show 1 + 3 * n = 3 * n + 1 from by ring,
        show n + 1 + n = 2 * n + 1 from by ring] at h
    exact h
  -- R5: (0, 1, 0, 3n+1, 0, n+1) → (2, 0, 0, 3n+1, 0, n)
  apply step_stepStar_stepPlus (c₂ := ⟨2, 0, 0, 3*n+1, 0, n⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show n + 1 = n + 1 from rfl]
    simp [fm]
  -- Phase B: R3+R2 chain (3n+1) rounds
  -- (2, 0, 0, 3n+1, 0, n) →* (2, 0, 0, 0, 6n+2, 4n+1)
  apply stepStar_trans (c₂ := ⟨2, 0, 0, 0, 6*n+2, 4*n+1⟩)
  · have h := r3r2_chain (3*n+1) 0 0 n
    simp only [Nat.zero_add, Nat.mul_zero] at h
    have he : 2 * (3 * n + 1) = 6 * n + 2 := by ring
    have hf : n + (3 * n + 1) = 4 * n + 1 := by ring
    rw [he, hf] at h
    exact h
  -- Two R3 steps: (2, 0, 0, 0, 6n+2, 4n+1) → (1, 0, 1, 0, 6n+3, 4n+2) → (0, 0, 2, 0, 6n+4, 4n+3)
  apply stepStar_trans (c₂ := ⟨0, 0, 2, 0, 6*n+4, 4*n+3⟩)
  · rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    ring_nf; finish
  -- Phase C: consume c=2
  -- (0, 0, 2, 0, 6n+4, 4n+3) →* (0, 0, 0, 0, 6n+4, 4n+3)
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 0, 6*n+4, 4*n+3⟩)
  · have h := c_consume (6*n+2) (4*n+3)
    rw [show 6 * n + 2 + 2 = 6 * n + 4 from by ring] at h
    exact h
  -- Phase D: e drain
  -- (0, 0, 0, 0, 6n+4, 4n+3) →* (0, 6n+4, 0, 6n+4, 0, 4n+3)
  have h := e_drain (6*n+4) 0 0 (4*n+3)
  rw [show 0 + (6 * n + 4) = 6 * n + 4 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 1, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 3*n+1, 0, 3*n+1, 0, 2*n+1⟩) 0
  intro n
  refine ⟨2*n+1, ?_⟩
  show ⟨0, 3*n+1, 0, 3*n+1, 0, 2*n+1⟩ [fm]⊢⁺ ⟨0, 3*(2*n+1)+1, 0, 3*(2*n+1)+1, 0, 2*(2*n+1)+1⟩
  rw [show 3 * (2 * n + 1) + 1 = 6 * n + 4 from by ring,
      show 2 * (2 * n + 1) + 1 = 4 * n + 3 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_192
