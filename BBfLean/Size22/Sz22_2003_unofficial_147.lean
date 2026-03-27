import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #147: [1/45, 245/2, 26/55, 33/7, 5/39]

Vector representation:
```
 0 -2 -1  0  0  0
-1  0  1  2  0  0
 1  0 -1  0 -1  1
 0  1  0 -1  1  0
 0 -1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_147

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+2, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R2+R3 loop: (1,1,0,d,k,f) →* (1,1,0,d+2k,0,f+k)
theorem r2r3_loop : ∀ k, ∀ d f, ⟨1, 1, 0, d, k, f⟩ [fm]⊢* ⟨(1 : ℕ), 1, 0, d+2*k, 0, f+k⟩ := by
  intro k; induction k with
  | zero => intro d f; exists 0
  | succ k ih =>
    intro d f
    step fm
    step fm
    apply stepStar_trans (ih (d + 2) (f + 1))
    ring_nf; finish

-- R4 drain: (0,b,0,d,e,f) →* (0,b+d,0,0,e+d,f)
theorem r4_drain : ∀ d, ∀ b e f, ⟨0, b, 0, d, e, f⟩ [fm]⊢* ⟨(0 : ℕ), b+d, 0, 0, e+d, f⟩ := by
  intro d; induction d with
  | zero => intro b e f; exists 0
  | succ d ih =>
    intro b e f
    step fm
    apply stepStar_trans (ih (b + 1) (e + 1) f)
    ring_nf; finish

-- R5+R1 drain: (0,3j+2,0,0,e,f+j) →* (0,2,0,0,e,f) when f+j≥j
theorem r5r1_drain : ∀ j, ∀ e f, ⟨0, 3*j+2, 0, 0, e, f+j⟩ [fm]⊢* ⟨(0 : ℕ), 2, 0, 0, e, f⟩ := by
  intro j; induction j with
  | zero => intro e f; exists 0
  | succ j ih =>
    intro e f
    -- b = 3*(j+1)+2 = 3j+5, f_val = f+j+1
    rw [show 3 * (j + 1) + 2 = (3 * j + 2 + 2) + 1 from by ring,
        show f + (j + 1) = (f + j) + 1 from by ring]
    -- R5: b≥1, f≥1 → (0,3j+4,1,0,e,f+j)
    step fm
    -- Now b=3j+4≥2 and c=1: R1 fires
    rw [show 3 * j + 2 + 2 = (3 * j + 2) + 2 from by ring]
    step fm
    -- Now (0,3j+2,0,0,e,f+j)
    exact ih e f

-- Main transition
theorem main_trans (k f : ℕ) :
    ⟨1, 1, 0, 0, 3*k+2, f⟩ [fm]⊢⁺ ⟨(1 : ℕ), 1, 0, 0, 6*k+5, f+k+1⟩ := by
  -- Phase 1: R2+R3 loop (3k+2 iterations)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 1, 0, 2*(3*k+2), 0, f+3*k+2⟩)
  · have h := r2r3_loop (3*k+2) 0 f
    rw [show (0 : ℕ) + 2 * (3 * k + 2) = 2 * (3 * k + 2) from by ring] at h
    exact h
  -- Phase 2: final R2
  apply step_stepStar_stepPlus
    (c₂ := ⟨0, 1, 1, 2*(3*k+2)+2, 0, f+3*k+2⟩)
  · show fm ⟨1, 1, 0, 2 * (3 * k + 2), 0, f + (3 * k + 2)⟩ =
        some ⟨0, 1, 1, 2 * (3 * k + 2) + 2, 0, f + (3 * k + 2)⟩
    simp [fm]
  -- Phase 3: R4 + R1 (2 steps)
  -- (0,1,1,6k+6,0,f+3k+2) → R4 → (0,2,1,6k+5,1,f+3k+2) → R1 → (0,0,0,6k+5,1,f+3k+2)
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 6*k+5, 1, f+3*k+2⟩)
  · rw [show 2 * (3 * k + 2) + 2 = (6 * k + 5) + 1 from by ring]
    step fm
    step fm
    finish
  -- Phase 4: R4 drain (6k+5 steps)
  -- (0,0,0,6k+5,1,f+3k+2) →* (0,6k+5,0,0,6k+6,f+3k+2)
  apply stepStar_trans (c₂ := ⟨0, 6*k+5, 0, 0, 6*k+6, f+3*k+2⟩)
  · have h := r4_drain (6*k+5) 0 1 (f+3*k+2)
    rw [show (0 : ℕ) + (6 * k + 5) = 6 * k + 5 from by ring,
        show 1 + (6 * k + 5) = 6 * k + 6 from by ring] at h
    exact h
  -- Phase 5: R5+R1 drain (2k+1 iterations)
  -- (0,6k+5,0,0,6k+6,f+3k+2) →* (0,2,0,0,6k+6,f+k+1)
  -- Note: 6k+5 = 3*(2k+1)+2 and f+3k+2 = (f+k+1)+(2k+1)
  apply stepStar_trans (c₂ := ⟨0, 2, 0, 0, 6*k+6, f+k+1⟩)
  · have h := r5r1_drain (2*k+1) (6*k+6) (f+k+1)
    rw [show 3 * (2 * k + 1) + 2 = 6 * k + 5 from by ring,
        show f + k + 1 + (2 * k + 1) = f + 3 * k + 2 from by ring] at h
    exact h
  -- Phase 6: R5 + R3
  -- (0,2,0,0,6k+6,f+k+1) → R5 → (0,1,1,0,6k+6,f+k) → R3 → (1,1,0,0,6k+5,f+k+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show f + k + 1 = (f + k) + 1 from by ring]
  step fm
  rw [show 6 * k + 6 = (6 * k + 5) + 1 from by ring]
  step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 1, 0, 0, 2, 1⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, f⟩ ↦ ⟨1, 1, 0, 0, 3*k+2, f⟩) ⟨0, 1⟩
  intro ⟨k, f⟩
  refine ⟨⟨2*k+1, f+k+1⟩, ?_⟩
  show ⟨1, 1, 0, 0, 3 * k + 2, f⟩ [fm]⊢⁺ ⟨1, 1, 0, 0, 3 * (2 * k + 1) + 2, f + k + 1⟩
  rw [show 3 * (2 * k + 1) + 2 = 6 * k + 5 from by ring]
  exact main_trans k f

end Sz22_2003_unofficial_147
