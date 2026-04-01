import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1190: [5/6, 49/2, 484/35, 3/11, 22/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  2
 0  1  0  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1190

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- Phase 1: Move e to b. (0, b, 0, d, e+k) →* (0, b+k, 0, d, e)
theorem e_to_b : ∀ k b d, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- Phase 3: Main loop. (R1 x2, R3) repeated k times.
-- (2, 2k+B, C, D+k, E) →* (2, B, C+k, D, E+2k)
theorem main_loop : ∀ k B C D E,
    ⟨(2 : ℕ), 2 * k + B, C, D + k, E⟩ [fm]⊢* ⟨(2 : ℕ), B, C + k, D, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro B C D E
  · ring_nf; finish
  · rw [show 2 * (k + 1) + B = (2 * k + B) + 1 + 1 from by ring,
        show D + (k + 1) = (D + k) + 1 from by ring]
    step fm  -- R1
    step fm  -- R1
    rw [show D + k + 1 = (D + k) + 1 from by ring]
    step fm  -- R3
    apply stepStar_trans (ih B (C + 1) D (E + 2))
    ring_nf; finish

-- Phase 4: R2/R3 drain. (R2 x2, R3) repeated k times.
-- (2, 0, c+k, d, e) →* (2, 0, c, d+3k, e+2k)
theorem r2r3_drain : ∀ k c d e,
    ⟨(2 : ℕ), 0, c + k, d, e⟩ [fm]⊢* ⟨(2 : ℕ), 0, c, d + 3 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm  -- R2: (1, 0, c+k+1, d+2, e)
    step fm  -- R2: (0, 0, c+k+1, d+4, e)
    rw [show d + 4 = (d + 3) + 1 from by ring,
        show c + k + 1 = (c + k) + 1 from by ring]
    step fm  -- R3: (2, 0, c+k, d+3, e+2)
    apply stepStar_trans (ih c (d + 3) (e + 2))
    ring_nf; finish

-- Main transition: C(n) →⁺ C(2n+1) where C(n) = (0, 0, 0, 2n+3, 2n+1)
theorem main_trans : ∀ n, ⟨(0 : ℕ), 0, 0, 2 * n + 3, 2 * n + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 4 * n + 5, 4 * n + 3⟩ := by
  intro n
  -- Phase 1: e_to_b
  rw [show (2 * n + 1 : ℕ) = 0 + (2 * n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * n + 1) 0 (2 * n + 3) (e := 0))
  simp only [Nat.zero_add]
  -- Phase 2: opening (R5, R1, R3)
  rw [show (2 * n + 1 : ℕ) = (2 * n) + 1 from by ring]
  step fm  -- R5: (1, 2n+1, 0, 2n+2, 1)
  rw [show (2 * n + 1 : ℕ) = (2 * n) + 1 from by ring]
  step fm  -- R1: (0, 2n, 1, 2n+2, 1)
  rw [show (2 * n + 2 : ℕ) = (2 * n + 1) + 1 from by ring]
  step fm  -- R3: (2, 2n, 0, 2n+1, 3)
  -- State: (2, 2n, 0, 2n+1, 3). Need to match main_loop(n, 0, 0, n+1, 3).
  -- main_loop expects (2, 2*n+0, 0, (n+1)+n, 3)
  rw [show (2 * n : ℕ) = 2 * n + 0 from by ring,
      show (2 * n + 1 : ℕ) = (n + 1) + n from by ring]
  apply stepStar_trans (main_loop n 0 0 (n + 1) 3)
  -- After main_loop: (2, 0, 0+n, n+1, 3+2n) = (2, 0, n, n+1, 2n+3)
  rw [show (0 + n : ℕ) = 0 + n from by ring,
      show (3 + 2 * n : ℕ) = 2 * n + 3 from by ring]
  apply stepStar_trans (r2r3_drain n 0 (n + 1) (2 * n + 3))
  -- After drain: (2, 0, 0, n+1+3n, 2n+3+2n) = (2, 0, 0, 4n+1, 4n+3)
  rw [show n + 1 + 3 * n = (4 * n + 1 : ℕ) from by ring,
      show 2 * n + 3 + 2 * n = (4 * n + 3 : ℕ) from by ring]
  -- Phase 5: final R2 x2
  step fm  -- R2: (1, 0, 0, 4n+3, 4n+3)
  step fm  -- R2: (0, 0, 0, 4n+5, 4n+3)
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 1⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n + 3, 2 * n + 1⟩) 0
  intro n; refine ⟨2 * n + 1, ?_⟩
  rw [show 2 * (2 * n + 1) + 3 = 4 * n + 5 from by ring,
      show 2 * (2 * n + 1) + 1 = 4 * n + 3 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1190
