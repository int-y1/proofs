import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #307: [15/2, 44/63, 7/165, 21/5, 1/3]

Vector representation:
```
-1  1  1  0  0
 2 -2  0 -1  1
 0 -1 -1  1 -1
 0  1 -1  1  0
 0 -1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_307

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+2, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b+1, c+1, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- Phase 1: Build phase. Each iteration does R2,R1,R1.
-- (0, 2, c, d+k, e) →* (0, 2, c+2k, d, e+k)
theorem build_phase : ∀ k c d e,
    ⟨0, 2, c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), 2, c + 2 * k, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase 2: Drain via alternating R3,R4.
-- (0, 1, 2k+1, d, k) →* (0, 2, 0, d+2k+1, 0)
-- Each iteration: R3 gives (0, 0, 2k, d+1, k-1), R4 gives (0, 1, 2k-1, d+2, k-1)
-- Final step when k=0: R4 gives (0, 2, 0, d+1, 0)
theorem drain_phase : ∀ k d,
    ⟨0, 1, 2 * k + 1, d, k⟩ [fm]⊢* ⟨(0 : ℕ), 2, 0, d + 2 * k + 1, 0⟩ := by
  intro k; induction k with
  | zero =>
    intro d
    -- (0, 1, 1, d, 0): a=0, b=1, c=1, e=0. Rule 3 needs e≥1, no. Rule 4: c≥1, yes.
    step fm; finish
  | succ k ih =>
    intro d
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    -- R3: (0, 1, (2k+1)+1+1, d, (k+1)) needs b≥1,c≥1,e≥1
    -- = (0, 0+1, (2k+2)+1, d, k+1) → (0, 0, 2k+2, d+1, k)
    rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    -- R4: (0, 0, 2k+2, d+1, k) needs c≥1
    -- = (0, 0, (2k+1)+1, d+1, k) → (0, 1, 2k+1, d+2, k)
    rw [show 2 * k + 1 + 1 = (2 * k + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- Main transition: (0, 2, 0, D+1, 0) ⊢⁺ (0, 2, 0, 2*(D+1), 0)
theorem main_trans (D : ℕ) : ⟨0, 2, 0, D + 1, 0⟩ [fm]⊢⁺ ⟨0, 2, 0, 2 * (D + 1), 0⟩ := by
  -- Phase 1: build_phase with c=0, e=0, k=D+1
  -- (0, 2, 0, D+1, 0) →* (0, 2, 2*(D+1), 0, D+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2, 2 * (D + 1), 0, D + 1⟩)
  · have h := build_phase (D + 1) 0 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: First R3 step
  -- (0, 2, 2*(D+1), 0, D+1) = (0, 1+1, (2*D+1)+1, 0, D+1)
  -- R3: → (0, 1, 2*D+1, 1, D)
  -- Then drain_phase: (0, 1, 2*D+1, 1, D) →* (0, 2, 0, 1+2*D+1, 0) = (0, 2, 0, 2*(D+1), 0)
  rw [show 2 * (D + 1) = (2 * D + 1) + 1 from by ring,
      show (D : ℕ) + 1 = D + 1 from rfl]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 1 + 1, (2 * D + 1) + 1, 0, D + 1⟩ = some ⟨0, 1, 2 * D + 1, 1, D⟩
    simp [fm]
  · have h := drain_phase D 1
    rw [show 1 + 2 * D + 1 = 2 * (D + 1) from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 2, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun D ↦ ⟨0, 2, 0, D + 2, 0⟩) 0
  intro D
  refine ⟨2 * D + 2, ?_⟩
  show ⟨0, 2, 0, D + 2, 0⟩ [fm]⊢⁺ ⟨0, 2, 0, 2 * D + 2 + 2, 0⟩
  rw [show D + 2 = (D + 1) + 1 from by ring,
      show 2 * D + 2 + 2 = 2 * ((D + 1) + 1) from by ring]
  exact main_trans (D + 1)

end Sz22_2003_unofficial_307
