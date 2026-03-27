import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #187: [1/6, 1925/2, 2/91, 39/5, 4/33]

Vector representation:
```
-1 -1  0  0  0  0
-1  0  2  1  1  0
 1  0  0 -1  0 -1
 0  1 -1  0  0  1
 2 -1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_187

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | _ => none

-- R3/R2 interleave: each iteration applies R3 then R2, consuming one f and adding 2 to c, 1 to e.
theorem r3r2_loop : ∀ k C E F, ⟨0, 0, C, 2, E, F+k⟩ [fm]⊢* ⟨(0 : ℕ), 0, C+2*k, 2, E+k, F⟩ := by
  intro k; induction k with
  | zero => intro C E F; exists 0
  | succ k ih =>
    intro C E F
    rw [show F + (k + 1) = (F + k) + 1 from by ring]
    rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R4 chain: c → b, f increases correspondingly.
theorem r4_chain : ∀ k B C E F, ⟨0, B, C+k, 0, E, F⟩ [fm]⊢* ⟨(0 : ℕ), B+k, C, 0, E, F+k⟩ := by
  intro k; induction k with
  | zero => intro B C E F; exists 0
  | succ k ih =>
    intro B C E F
    rw [show C + (k + 1) = (C + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- R5/R1/R1 loop: each cycle removes 3 from b and 1 from e.
theorem r5r1r1_loop : ∀ k E F, ⟨0, 3*k+1, 0, 0, E+k+1, F⟩ [fm]⊢* ⟨(2 : ℕ), 0, 0, 0, E, F⟩ := by
  intro k; induction k with
  | zero =>
    intro E F
    rw [show E + 0 + 1 = E + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring,
        show E + 1 = E + 1 from by ring]
    step fm; finish
  | succ k ih =>
    intro E F
    rw [show 3 * (k + 1) + 1 = (3 * k + 1) + 1 + 1 + 1 from by ring,
        show E + (k + 1) + 1 = (E + k + 1) + 1 from by ring]
    -- R5: (0, 3k+4, 0, 0, E+k+2, F) → (2, 3k+3, 0, 0, E+k+1, F)
    step fm
    -- R1: (2, 3k+3, 0, 0, E+k+1, F) → (1, 3k+2, 0, 0, E+k+1, F)
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show 3 * k + 1 + 1 + 1 = (3 * k + 1 + 1) + 1 from by ring]
    step fm
    -- R1: (1, 3k+2, 0, 0, E+k+1, F) → (0, 3k+1, 0, 0, E+k+1, F)
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 3 * k + 1 + 1 = (3 * k + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Main transition: (2, 0, 0, 0, n, 3n+1) →⁺ (2, 0, 0, 0, 2n+1, 6n+4)
theorem main_trans (n : ℕ) : ⟨2, 0, 0, 0, n, 3*n+1⟩ [fm]⊢⁺ ⟨(2 : ℕ), 0, 0, 0, 2*n+1, 6*n+4⟩ := by
  -- Phase A: (2, 0, 0, 0, n, 3n+1) →* (0, 0, 6n+6, 2, 4n+3, 0)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, 2, 1, n + 1, 3 * n + 1⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring]; simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 0, 4, 2, n + 2, 3 * n + 1⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm; finish
  apply stepStar_trans (c₂ := ⟨0, 0, 6 * n + 6, 2, 4 * n + 3, 0⟩)
  · have h := r3r2_loop (3 * n + 1) 4 (n + 2) 0
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  -- Phase B: (0, 0, 6n+6, 2, 4n+3, 0) →* (0, 0, 6n+4, 0, 4n+3, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, 6 * n + 4, 0, 4 * n + 3, 0⟩)
  · -- R4: (0, 0, 6n+6, 2, 4n+3, 0) → (0, 1, 6n+5, 2, 4n+3, 1)
    rw [show 6 * n + 6 = (6 * n + 5) + 1 from by ring]
    step fm
    -- R3: (0, 1, 6n+5, 2, 4n+3, 1) → (1, 1, 6n+5, 1, 4n+3, 0)
    rw [show (2 : ℕ) = 0 + 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    -- R1: (1, 1, 6n+5, 1, 4n+3, 0) → (0, 0, 6n+5, 1, 4n+3, 0)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    -- R4: (0, 0, 6n+5, 1, 4n+3, 0) → (0, 1, 6n+4, 1, 4n+3, 1)
    rw [show 6 * n + 5 = (6 * n + 4) + 1 from by ring]
    step fm
    -- R3: (0, 1, 6n+4, 1, 4n+3, 1) → (1, 1, 6n+4, 0, 4n+3, 0)
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    -- R1: (1, 1, 6n+4, 0, 4n+3, 0) → (0, 0, 6n+4, 0, 4n+3, 0)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    finish
  -- Phase C: (0, 0, 6n+4, 0, 4n+3, 0) →* (0, 6n+4, 0, 0, 4n+3, 6n+4)
  apply stepStar_trans (c₂ := ⟨0, 6 * n + 4, 0, 0, 4 * n + 3, 6 * n + 4⟩)
  · have h := r4_chain (6 * n + 4) 0 0 (4 * n + 3) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase D: (0, 6n+4, 0, 0, 4n+3, 6n+4) →* (2, 0, 0, 0, 2n+1, 6n+4)
  -- Use r5r1r1_loop with k = 2n+1, E = 2n+1, F = 6n+4
  -- Need: 3*(2n+1)+1 = 6n+4 ✓ and E+k+1 = (2n+1)+(2n+1)+1 = 4n+3 ✓
  · have h := r5r1r1_loop (2 * n + 1) (2 * n + 1) (6 * n + 4)
    rw [show 3 * (2 * n + 1) + 1 = 6 * n + 4 from by ring,
        show 2 * n + 1 + (2 * n + 1) + 1 = 4 * n + 3 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0, 1⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2, 0, 0, 0, n, 3 * n + 1⟩) 0
  intro n
  refine ⟨2 * n + 1, ?_⟩
  show ⟨2, 0, 0, 0, n, 3 * n + 1⟩ [fm]⊢⁺ ⟨2, 0, 0, 0, 2 * n + 1, 3 * (2 * n + 1) + 1⟩
  rw [show 3 * (2 * n + 1) + 1 = 6 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_187
