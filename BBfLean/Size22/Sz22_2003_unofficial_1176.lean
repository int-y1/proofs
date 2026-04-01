import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1176: [5/6, 49/2, 44/35, 3/11, 18/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  1  0  0 -1
 1  2  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1176

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | _ => none

-- R4 repeated: move e to b. (0, b, 0, d, e+k) →* (0, b+k, 0, d, e)
theorem e_to_b : ∀ k b, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

-- Interleave k rounds: (0, 2*k+b, c+1, d+k, e) →* (0, b, c+k+1, d, e+k)
-- Using 2*k+b order so it matches what step fm produces (2*n+1).
theorem interleave : ∀ k b c d e,
    ⟨(0 : ℕ), 2 * k + b, c + 1, d + k, e⟩ [fm]⊢* ⟨0, b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · ring_nf; finish
  · rw [show 2 * (k + 1) + b = 2 * k + (b + 2) from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    -- Now at (0, b+2, c+k+1, d+1, e+k)
    rw [show c + k + 1 = (c + k) + 1 from by ring]
    -- R3, R1, R1
    step fm; step fm; step fm
    ring_nf; finish

-- Final transition: R3, R1, R2. (0, 1, c+1, d+1, e) →* (0, 0, c+1, d+2, e+1)
theorem final_trans : ⟨(0 : ℕ), 1, c + 1, d + 1, e⟩ [fm]⊢* ⟨0, 0, c + 1, d + 2, e + 1⟩ := by
  step fm; step fm; step fm; finish

-- Drain k+1 rounds: (0, 0, k+1, d+1, e) →* (0, 0, 0, d+3*k+4, e+k+1)
theorem drain : ∀ k d e,
    ⟨(0 : ℕ), 0, k + 1, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k + 4, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · -- R3, R2, R2
    step fm; step fm; step fm; finish
  · -- (0, 0, k+2, d+1, e). R3, R2, R2 gives (0, 0, k+1, d+4, e+1)
    rw [show (k + 1 : ℕ) + 1 = (k + 1) + 1 from rfl]
    step fm; step fm; step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d + 3) (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, (n+1)^2 + 1, 2*n) →⁺ (0, 0, 0, (n+2)^2 + 1, 2*(n+1))
theorem main_trans (n : ℕ) : ⟨(0 : ℕ), 0, 0, (n + 1) ^ 2 + 1, 2 * n⟩ [fm]⊢⁺
    ⟨0, 0, 0, (n + 2) ^ 2 + 1, 2 * (n + 1)⟩ := by
  -- Phase 1: e_to_b: (0, 0, 0, (n+1)^2+1, 0+2*n) →* (0, 0+2*n, 0, (n+1)^2+1, 0)
  rw [show (2 * n : ℕ) = 0 + 2 * n from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * n) 0 (d := (n + 1) ^ 2 + 1) (e := 0))
  -- Now at (0, 2*n, 0, (n+1)^2+1, 0). Do R5 and R1.
  rw [show (0 : ℕ) + 2 * n = 2 * n from by ring,
      show (n + 1) ^ 2 + 1 = (n + 1) ^ 2 + 0 + 1 from by ring]
  step fm -- R5: (1, 2*n+2, 0, (n+1)^2, 0)
  step fm -- R1: (0, 2*n+1, 1, (n+1)^2, 0)
  -- After step fm, the state is (0, 2*n+1, 1, (n+1)^2, 0), goal is ⊢*.
  -- Rewrite d to match interleave form.
  rw [show (n + 1) ^ 2 = (n * n + n + 1) + n from by ring]
  apply stepStar_trans (interleave n 1 0 (n * n + n + 1) 0)
  -- Now at (0, 1, 0+n+1, n*n+n+1, 0+n) = (0, 1, n+1, n*n+n+1, n), goal is ⊢*
  rw [show 0 + n + 1 = n + 1 from by ring,
      show n * n + n + 1 = (n * n + n) + 1 from by ring,
      show 0 + n = n from by ring]
  apply stepStar_trans (final_trans (c := n) (d := n * n + n) (e := n))
  -- Now at (0, 0, n+1, n*n+n+2, n+1), goal is ⊢*
  rw [show n * n + n + 2 = (n * n + n + 1) + 1 from by ring]
  apply stepStar_trans (drain n (n * n + n + 1) (n + 1))
  -- Now need: (0, 0, 0, n*n+n+1+3*n+4, n+1+n+1) ⊢* (0, 0, 0, (n+2)^2+1, 2*(n+1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, (0 + 1) ^ 2 + 1, 2 * 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, (n + 1) ^ 2 + 1, 2 * n⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1176
