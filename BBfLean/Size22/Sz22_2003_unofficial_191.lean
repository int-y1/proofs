import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #191: [1/6, 2/35, 7865/2, 21/11, 4/39]

Vector representation:
```
-1 -1  0  0  0  0
 1  0 -1 -1  0  0
-1  0  1  0  2  1
 0  1  0  1 -1  0
 2 -1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_191

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+2, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | _ => none

-- R3+R2 loop: (2, 0, 0, d+k, e, f) ⊢* (2, 0, 0, d, e+2*k, f+k)
theorem r3r2_loop : ∀ k d e f,
    (⟨2, 0, 0, d + k, e, f⟩ : Q) [fm]⊢* ⟨2, 0, 0, d, e + 2 * k, f + k⟩ := by
  intro k; induction k with
  | zero => intro d e f; exists 0
  | succ k ih =>
    intro d e f
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih d (e + 2) (f + 1))
    ring_nf; finish

-- Cleanup: (0, 0, 2, 0, e+2, f) ⊢* (0, 0, 0, 0, e, f) in 6 steps
theorem cleanup : ∀ e f,
    (⟨0, 0, 2, 0, e + 2, f⟩ : Q) [fm]⊢* ⟨0, 0, 0, 0, e, f⟩ := by
  intro e f
  step fm; step fm; step fm; step fm; step fm; step fm; finish

-- R4 drain: (0, b, 0, d, e+k, f) ⊢* (0, b+k, 0, d+k, e, f)
theorem r4_drain : ∀ k b d e f,
    (⟨0, b, 0, d, e + k, f⟩ : Q) [fm]⊢* ⟨0, b + k, 0, d + k, e, f⟩ := by
  intro k; induction k with
  | zero => intro b d e f; exists 0
  | succ k ih =>
    intro b d e f
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) (d + 1) e f)
    ring_nf; finish

-- R5+R1+R1 drain: (0, 3*k+1, 0, d, 0, k+r+1) ⊢* (2, 0, 0, d, 0, r)
theorem r5r1r1_drain : ∀ k d r,
    (⟨0, 3 * k + 1, 0, d, 0, k + r + 1⟩ : Q) [fm]⊢* ⟨2, 0, 0, d, 0, r⟩ := by
  intro k; induction k with
  | zero =>
    intro d r
    simp only [Nat.zero_add]
    step fm; finish
  | succ k ih =>
    intro d r
    rw [show 3 * (k + 1) + 1 = (3 * k + 4) from by ring,
        show (k + 1) + r + 1 = (k + r + 2) from by ring,
        show 3 * k + 4 = (3 * k + 1) + 3 from by ring,
        show k + r + 2 = (k + r + 1) + 1 from by ring]
    step fm  -- R5: (2, 3k+3, 0, d, 0, k+r+1)
    step fm  -- R1: (1, 3k+2, 0, d, 0, k+r+1)
    step fm  -- R1: (0, 3k+1, 0, d, 0, k+r+1)
    exact ih d r

-- Main transition: (2, 0, 0, 3*f+1, 0, f) ⊢⁺ (2, 0, 0, 6*f+4, 0, 2*f+1)
theorem main_trans : ∀ g,
    (⟨2, 0, 0, 3 * g + 1, 0, g⟩ : Q) [fm]⊢⁺ ⟨2, 0, 0, 6 * g + 4, 0, 2 * g + 1⟩ := by
  intro g
  -- Phase 1: R3R2 loop (3g+1 iterations, first step explicit for stepPlus)
  -- First two steps: R3+R2 manually
  rw [show (3 : ℕ) * g + 1 = 0 + (3 * g) + 1 from by ring]
  apply step_stepStar_stepPlus
  · unfold fm; rfl  -- R3: (1, 0, 1, 3g+1, 2, g+1)
  step fm  -- R2: (2, 0, 0, 3g, 2, g+1)
  -- Remaining R3R2 loop (3g iterations)
  apply stepStar_trans (r3r2_loop (3 * g) 0 2 (g + 1))
  -- Now at (2, 0, 0, 0, 6g+2, 4g+1)
  rw [show 2 + 2 * (3 * g) = 6 * g + 2 from by ring,
      show g + 1 + 3 * g = 4 * g + 1 from by ring]
  -- Phase 2: Two more R3 steps
  step fm  -- R3: (1, 0, 1, 0, 6g+4, 4g+2)
  step fm  -- R3: (0, 0, 2, 0, 6g+6, 4g+3)
  -- Phase 3: Cleanup
  apply stepStar_trans
  · rw [show 6 * g + 6 = (6 * g + 4) + 2 from by ring]
    exact cleanup (6 * g + 4) (4 * g + 3)
  -- Now at (0, 0, 0, 0, 6g+4, 4g+3)
  -- Phase 4: R4 drain (6g+4 steps)
  apply stepStar_trans
  · rw [show (6 : ℕ) * g + 4 = 0 + (6 * g + 4) from by ring]
    exact r4_drain (6 * g + 4) 0 0 0 (4 * g + 3)
  -- Now at (0, 6g+4, 0, 6g+4, 0, 4g+3)
  rw [show 0 + (6 * g + 4) = 6 * g + 4 from by ring]
  -- Phase 5: R5+R1+R1 drain
  have h5 := r5r1r1_drain (2 * g + 1) (6 * g + 4) (2 * g + 1)
  rw [show 3 * (2 * g + 1) + 1 = 6 * g + 4 from by ring,
      show (2 * g + 1) + (2 * g + 1) + 1 = 4 * g + 3 from by ring] at h5
  exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ g, q = ⟨2, 0, 0, 3 * g + 1, 0, g⟩)
  · intro c ⟨g, hq⟩; subst hq
    exact ⟨⟨2, 0, 0, 6 * g + 4, 0, 2 * g + 1⟩,
           ⟨2 * g + 1, by ring_nf⟩,
           main_trans g⟩
  · exact ⟨0, by ring_nf⟩

end Sz22_2003_unofficial_191
