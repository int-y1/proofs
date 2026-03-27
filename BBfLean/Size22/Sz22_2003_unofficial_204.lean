import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #204: [1/6, 35/2, 4/55, 3/5, 242/21]

Vector representation:
```
-1 -1  0  0  0
-1  0  1  1  0
 2  0 -1  0 -1
 0  1 -1  0  0
 1 -1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_204

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R4 repeated: drain c into b (when a=0, e=0)
theorem r4_repeat : ∀ k b c d,
    ⟨0, b, c + k, d, 0⟩ [fm]⊢* ⟨(0 : ℕ), b + k, c, d, 0⟩ := by
  intro k; induction k with
  | zero => intro b c d; simp; exists 0
  | succ k ih =>
    intro b c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c d)
    ring_nf; finish

-- R5/R1 drain: from (0, 2k+1, 0, d+k+1, e) to (1, 0, 0, d, e+2k+2)
theorem r5r1_drain : ∀ k d e,
    ⟨0, 2 * k + 1, 0, d + k + 1, e⟩ [fm]⊢* ⟨(1 : ℕ), 0, 0, d, e + 2 * k + 2⟩ := by
  intro k; induction k with
  | zero =>
    intro d e
    rw [show d + 0 + 1 = d + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm
    ring_nf; finish
  | succ k ih =>
    intro d e
    rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show d + (k + 1) + 1 = (d + k + 1) + 1 from by ring,
        show (2 * k + 2) + 1 = (2 * k + 2) + 1 from rfl]
    -- R5: (0, (2k+2)+1, 0, (d+k+1)+1, e) → (1, 2k+2, 0, d+k+1, e+2)
    step fm
    -- R1: (1, 2k+2, 0, d+k+1, e+2) = (0+1, (2k+1)+1, 0, d+k+1, e+2) → (0, 2k+1, 0, d+k+1, e+2)
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih d (e + 2))
    ring_nf; finish

-- R3/R2/R2 loop: from (0, 0, c+1, d, k+1) to (0, 0, c+k+2, d+2k+2, 0)
theorem r3r2r2_loop : ∀ k c d,
    ⟨0, 0, c + 1, d, k + 1⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + k + 2, d + 2 * k + 2, 0⟩ := by
  intro k; induction k with
  | zero =>
    intro c d
    -- (0, 0, c+1, d, 1): R3 → (2, 0, c, d, 0) → R2 → (1, 0, c+1, d+1, 0) → R2 → (0, 0, c+2, d+2, 0)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    ring_nf; finish
  | succ k ih =>
    intro c d
    rw [show k + 1 + 1 = (k + 1) + 1 from by ring,
        show (k + 1) + 1 = k + 1 + 1 from by ring]
    -- R3: (0, 0, c+1, d, k+2) → (2, 0, c, d, k+1)
    -- but we need e+1 pattern, so k+2 = (k+1) + 1
    rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm
    -- R2: (2, 0, c, d, k+1) → (1, 0, c+1, d+1, k+1)
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    -- R2: (1, 0, c+1, d+1, k+1) → (0, 0, c+2, d+2, k+1)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) (d + 2))
    ring_nf; finish

-- Main transition: (0, 0, 2m+1, d+m+1, 0) ⊢⁺ (0, 0, 2m+3, d+4m+5, 0)
theorem main_trans (m d : ℕ) :
    ⟨0, 0, 2 * m + 1, d + m + 1, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 2 * m + 3, d + 4 * m + 5, 0⟩ := by
  -- Phase A: R4 × (2m+1): → (0, 2m+1, 0, d+m+1, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2 * m + 1, 0, d + m + 1, 0⟩)
  · rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
    exact r4_repeat (2 * m + 1) 0 0 (d + m + 1)
  -- Phase B: R5/R1 drain: → (1, 0, 0, d, 2m+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 0, 0, d, 2 * m + 2⟩)
  · have h := r5r1_drain m d 0
    rw [show 0 + 2 * m + 2 = 2 * m + 2 from by ring] at h
    exact h
  -- Phase C: R2: (1, 0, 0, d, 2m+2) → (0, 0, 1, d+1, 2m+2)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, 1, d + 1, 2 * m + 2⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring]
    simp [fm]
  -- Phase D: R3/R2/R2 loop: (0, 0, 1, d+1, 2m+2) → (0, 0, 2m+3, d+4m+5, 0)
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_loop (2 * m + 1) 0 (d + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 1, 0⟩) (by unfold c₀; execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, d⟩ ↦ ⟨0, 0, 2 * m + 1, d + m + 1, 0⟩) ⟨0, 0⟩
  intro ⟨m, d⟩
  refine ⟨⟨m + 1, d + 3 * m + 3⟩, ?_⟩
  show ⟨0, 0, 2 * m + 1, d + m + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * (m + 1) + 1, (d + 3 * m + 3) + (m + 1) + 1, 0⟩
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring,
      show (d + 3 * m + 3) + (m + 1) + 1 = d + 4 * m + 5 from by ring]
  exact main_trans m d

end Sz22_2003_unofficial_204
