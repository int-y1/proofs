import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1222: [5/6, 539/2, 52/55, 3/13, 15/7]

Vector representation:
```
-1 -1  1  0  0  0
-1  0  0  2  1  0
 2  0 -1  0 -1  1
 0  1  0  0  0 -1
 0  1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1222

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+2, e+1, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 chain: drain f to b
theorem f_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d, e, k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R1-R1-R3 chain: (2, b+2k, c, d, k, f) ->* (2, b, c+k, d, 0, f+k)
theorem r1r1r3_chain : ∀ k, ∀ b c d f,
    ⟨(2 : ℕ), b + 2 * k, c, d, k, f⟩ [fm]⊢* ⟨(2 : ℕ), b, c + k, d, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring]
    step fm
    step fm
    rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih b (c + 1) d (f + 1))
    ring_nf; finish

-- R3-R2-R2 chain: (0, 0, c+k, d, e+1, f) ->* (0, 0, c, d+4k, e+1+k, f+k)
theorem r3r2r2_chain : ∀ k, ∀ c d e f,
    ⟨(0 : ℕ), 0, c + k, d, e + 1, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + 4 * k, e + 1 + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show e + 1 + 1 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih c (d + 4) (e + 1) (f + 1))
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * n * n + 7 * n + 7, n + 2, 2 * n + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 2 * n * n + 11 * n + 16, n + 3, 2 * n + 4⟩ := by
  -- Phase 1: First R4 step (establishes ⊢⁺)
  rw [show (2 * n + 2 : ℕ) = (2 * n + 1) + 1 from by ring]
  step fm
  -- Remaining R4 steps
  apply stepStar_trans (f_to_b (2 * n + 1) 1 (2 * n * n + 7 * n + 7) (n + 2))
  rw [show 1 + (2 * n + 1) = 2 * n + 2 from by ring]
  -- Phase 2: R5 step
  rw [show (2 * n * n + 7 * n + 7 : ℕ) = (2 * n * n + 7 * n + 6) + 1 from by ring]
  step fm
  -- Phase 3: R3 step
  rw [show (n + 2 : ℕ) = (n + 1) + 1 from by ring]
  step fm
  -- State: (2, 2n+3, 0, 2n^2+7n+6, n+1, 1)
  -- Phase 4: R1-R1-R3 chain (n+1 rounds)
  rw [show (2 * n + 2 + 1 : ℕ) = 1 + 2 * (n + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (n + 1) 1 0 (2 * n * n + 7 * n + 6) 1)
  -- State: (2, 1, n+1, 2n^2+7n+6, 0, n+2)
  rw [show 0 + (n + 1) = n + 1 from by ring,
      show 1 + (n + 1) = n + 2 from by ring]
  -- Phase 5: R1 + R2
  step fm
  step fm
  -- State: (0, 0, n+2, 2n^2+7n+8, 1, n+2)
  -- Phase 6: R3-R2-R2 chain (n+2 rounds)
  -- Need to massage the state to match r3r2r2_chain signature
  have h6 := r3r2r2_chain (n + 2) 0 (2 * n * n + 7 * n + 6 + 2) 0 (0 + (n + 2))
  rw [show 0 + (n + 2) = n + 2 from by ring] at h6
  apply stepStar_trans h6
  rw [show 2 * n * n + 7 * n + 8 + 4 * (n + 2) = 2 * n * n + 11 * n + 16 from by ring,
      show 0 + 1 + (n + 2) = n + 3 from by ring,
      show (n + 2) + (n + 2) = 2 * n + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 7, 2, 2⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n * n + 7 * n + 7, n + 2, 2 * n + 2⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  rw [show 2 * (n + 1) * (n + 1) + 7 * (n + 1) + 7 = 2 * n * n + 11 * n + 16 from by ring,
      show n + 1 + 2 = n + 3 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1222
