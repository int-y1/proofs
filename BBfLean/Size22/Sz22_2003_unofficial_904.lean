import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #904: [4/15, 3/14, 275/2, 7/11, 3/5, 1/3]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0  0  1 -1
 0  1 -1  0  0
 0 -1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_904

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- R3 chain: (a+k, 0, c, 0, e) →* (a, 0, c+2*k, 0, e+k)
theorem r3_chain : ∀ k a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) (e + 1))
    ring_nf; finish

-- R4 chain: (0, 0, c, d, e+k) →* (0, 0, c, d+k, e)
theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) e)
    ring_nf; finish

-- R1-R2 chain: (a, 1, c+D, D, 0) →* (a+D, 1, c, 0, 0)
-- Each round: R1 fires (b=1,c≥1), then R2 fires (a≥1,d≥1)
theorem r1r2_chain : ∀ D a c, ⟨a, 1, c + D, D, 0⟩ [fm]⊢* ⟨a + D, 1, c, 0, 0⟩ := by
  intro D; induction' D with D ih <;> intro a c
  · exists 0
  · rw [show c + (D + 1) = (c + D) + 1 from by ring]
    step fm -- R1: (a+2, 0, c+D, D+1, 0)
    step fm -- R2: (a+1, 1, c+D, D, 0)
    apply stepStar_trans (ih (a + 1) c)
    ring_nf; finish

-- Main transition
theorem main_trans (k : ℕ) :
    ⟨2 * k + 5, 0, k * (k + 2), 0, 0⟩ [fm]⊢⁺ ⟨2 * k + 7, 0, (k + 1) * (k + 3), 0, 0⟩ := by
  -- Phase 1: R3 chain (2k+5 steps): →* (0, 0, k²+6k+10, 0, 2k+5)
  have ph1 : ⟨2 * k + 5, 0, k * (k + 2), 0, 0⟩ [fm]⊢*
             ⟨0, 0, k * k + 6 * k + 10, 0, 2 * k + 5⟩ := by
    have h := r3_chain (2 * k + 5) 0 (k * (k + 2)) 0; simp at h
    rw [show k * (k + 2) + 2 * (2 * k + 5) = k * k + 6 * k + 10 from by ring] at h
    exact h
  -- Phase 2: R4 chain (2k+5 steps): →* (0, 0, k²+6k+10, 2k+5, 0)
  have ph2 : ⟨0, 0, k * k + 6 * k + 10, 0, 2 * k + 5⟩ [fm]⊢*
             ⟨0, 0, k * k + 6 * k + 10, 2 * k + 5, 0⟩ := by
    have h := r4_chain (2 * k + 5) (k * k + 6 * k + 10) 0 0; simp at h; exact h
  -- Phase 3: R5 step: → (0, 1, k²+6k+9, 2k+5, 0)
  have ph3 : ⟨0, 0, k * k + 6 * k + 10, 2 * k + 5, 0⟩ [fm]⊢
             ⟨0, 1, k * k + 6 * k + 9, 2 * k + 5, 0⟩ := by
    rw [show k * k + 6 * k + 10 = (k * k + 6 * k + 9) + 1 from by ring]
    simp [fm]
  -- Phase 4: R1-R2 chain (2k+5 rounds)
  -- (0, 1, k²+6k+9, 2k+5, 0) →* (2k+5, 1, k²+4k+4, 0, 0)
  -- k²+6k+9 = k²+4k+4 + (2k+5)
  have ph4 : ⟨0, 1, k * k + 6 * k + 9, 2 * k + 5, 0⟩ [fm]⊢*
             ⟨2 * k + 5, 1, k * k + 4 * k + 4, 0, 0⟩ := by
    rw [show k * k + 6 * k + 9 = (k * k + 4 * k + 4) + (2 * k + 5) from by ring]
    have h := r1r2_chain (2 * k + 5) 0 (k * k + 4 * k + 4); simp at h; exact h
  -- Phase 5: Final R1
  -- (2k+5, 1, k²+4k+4, 0, 0) → (2k+7, 0, k²+4k+3, 0, 0) = (2k+7, 0, (k+1)(k+3), 0, 0)
  have ph5 : ⟨2 * k + 5, 1, k * k + 4 * k + 4, 0, 0⟩ [fm]⊢
             ⟨2 * k + 7, 0, (k + 1) * (k + 3), 0, 0⟩ := by
    rw [show k * k + 4 * k + 4 = ((k + 1) * (k + 3)) + 1 from by ring]
    simp [fm]
  -- Compose: ph1 ⊢* ph2 ⊢* (ph3 ⊢) (ph4 ⊢*) (ph5 ⊢)
  exact stepStar_stepPlus_stepPlus
    (stepStar_trans ph1 (stepStar_trans ph2 (step_stepStar ph3)))
    (stepStar_step_stepPlus ph4 ph5)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 0⟩)
  · execute fm 20
  · show ¬halts fm ⟨2 * 0 + 5, 0, 0 * (0 + 2), 0, 0⟩
    apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun k ↦ ⟨2 * k + 5, 0, k * (k + 2), 0, 0⟩) 0
    intro k; exact ⟨k + 1, main_trans k⟩
