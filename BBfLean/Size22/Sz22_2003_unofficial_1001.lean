import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1001: [4/15, 429/14, 55/2, 7/13, 21/11]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  1
-1  0  1  0  1  0
 0  0  0  1  0 -1
 0  1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1001

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R3 chain: (a+k, 0, c, 0, e, fv) →* (a, 0, c+k, 0, e+k, fv)
theorem r3_chain : ∀ k a c e fv, ⟨a + k, 0, c, 0, e, fv⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k, fv⟩ := by
  intro k; induction' k with k ih <;> intro a c e fv
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1) fv)
    ring_nf; finish

-- R4 chain: (0, 0, c, d, e, fv+k) →* (0, 0, c, d+k, e, fv)
theorem r4_chain : ∀ k c d e fv, ⟨0, 0, c, d, e, fv + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e, fv⟩ := by
  intro k; induction' k with k ih <;> intro c d e fv
  · exists 0
  · rw [show fv + (k + 1) = (fv + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) e fv)
    ring_nf; finish

-- R1+R2 interleaved chain:
-- (j, 1, c+n, d+n, e, fv) →* (j+n, 1, c, d, e+n, fv+n)
theorem r1r2_chain : ∀ n j c d e fv, ⟨j, 1, c + n, d + n, e, fv⟩ [fm]⊢* ⟨j + n, 1, c, d, e + n, fv + n⟩ := by
  intro n; induction' n with n ih <;> intro j c d e fv
  · exists 0
  · rw [show c + (n + 1) = (c + n) + 1 from by ring,
        show d + (n + 1) = (d + n) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (j + 1) c d (e + 1) (fv + 1))
    ring_nf; finish

-- Full cycle composition:
-- (f+1, 0, 0, 0, f*(f+1), f) →⁺ (f+2, 0, 0, 0, (f+1)*(f+2), f+1)
theorem main_trans (f : ℕ) : ⟨f + 1, 0, 0, 0, f * (f + 1), f⟩ [fm]⊢⁺ ⟨f + 2, 0, 0, 0, (f + 1) * (f + 2), f + 1⟩ := by
  -- Phase 1: R3 chain (f+1 times)
  -- Need: (f+1, 0, 0, 0, f*(f+1), f) →* (0, 0, f+1, 0, f*(f+1)+f+1, f)
  have phase1 : ⟨f + 1, 0, 0, 0, f * (f + 1), f⟩ [fm]⊢* ⟨0, 0, f + 1, 0, f * (f + 1) + (f + 1), f⟩ := by
    have := r3_chain (f + 1) 0 0 (f * (f + 1)) f
    simp at this; exact this
  -- Phase 2: R4 chain (f times)
  -- Need: (0, 0, f+1, 0, ..., f) →* (0, 0, f+1, f, ..., 0)
  have phase2 : ⟨0, 0, f + 1, 0, f * (f + 1) + (f + 1), f⟩ [fm]⊢* ⟨0, 0, f + 1, f, f * (f + 1) + (f + 1), 0⟩ := by
    have := r4_chain f (f + 1) 0 (f * (f + 1) + (f + 1)) 0
    simp at this; exact this
  -- Phase 3: R5 (1 step)
  -- (0, 0, f+1, f, E+1, 0) → (0, 1, f+1, f+1, E, 0) where E = f*(f+1)+f
  have phase3 : ⟨0, 0, f + 1, f, f * (f + 1) + (f + 1), 0⟩ [fm]⊢⁺ ⟨0, 1, f + 1, f + 1, f * (f + 1) + f, 0⟩ := by
    rw [show f * (f + 1) + (f + 1) = (f * (f + 1) + f) + 1 from by ring]
    step fm; finish
  -- Phase 4: R1R2 chain (f+1 rounds)
  have phase4 : ⟨0, 1, f + 1, f + 1, f * (f + 1) + f, 0⟩ [fm]⊢* ⟨f + 1, 1, 0, 0, f * (f + 1) + f + (f + 1), f + 1⟩ := by
    have := r1r2_chain (f + 1) 0 0 0 (f * (f + 1) + f) 0
    simp at this; exact this
  -- Phase 5+6: R3 then R1
  -- (f+1, 1, 0, 0, ..., f+1) → R3 → (f, 1, 1, 0, ..., f+1) → R1 → (f+2, 0, 0, 0, ..., f+1)
  have phase56 : ⟨f + 1, 1, 0, 0, f * (f + 1) + f + (f + 1), f + 1⟩ [fm]⊢⁺ ⟨f + 2, 0, 0, 0, (f + 1) * (f + 2), f + 1⟩ := by
    step fm
    step fm
    rw [show f * (f + 1) + f + (f + 1) + 1 = (f + 1) * (f + 2) from by ring]
    finish
  exact stepStar_stepPlus_stepPlus phase1
    (stepStar_stepPlus_stepPlus phase2
      (stepPlus_trans phase3
        (stepStar_stepPlus_stepPlus phase4 phase56)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2, 1⟩)
  · execute fm 6
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, (n + 1) * (n + 2), n + 1⟩) 0
  intro n; exists n + 1
  exact main_trans (n + 1)
