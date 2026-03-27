import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #605: [35/6, 121/2, 4/55, 3/7, 42/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 1  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_605

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _); ring_nf; finish

-- R3,R2,R2 repeated: drain c, each round (c+1,e+1) -> (c,e+4)
theorem c_drain : ∀ k c E, ⟨(0 : ℕ), 0, c + k, D, E + k⟩ [fm]⊢* ⟨0, 0, c, D, E + 4 * k⟩ := by
  intro k; induction' k with k h <;> intro c E
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show E + k + 4 = (E + 4) + k from by ring]
  apply stepStar_trans (h _ (E + 4))
  ring_nf; finish

-- Inner loop: from (2, 2+2*j, k, D, E+j) to (0, 0, k+j+2, D+2+2*j, E)
theorem inner_loop : ∀ j, ∀ k D E, ⟨(2 : ℕ), 2 + 2 * j, k, D, E + j⟩ [fm]⊢* ⟨0, 0, k + j + 2, D + 2 + 2 * j, E⟩ := by
  intro j; induction' j with j ih <;> intro k D E
  · step fm; step fm; ring_nf; finish
  rw [show 2 + 2 * (j + 1) = (2 + 2 * j) + 2 from by ring,
      show E + (j + 1) = (E + j) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- Main transition: C(n) = (0, 0, 0, 2*(n+1), n*n+3*n+4) ->+ C(n+1)
theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * (n + 1), n * n + 3 * n + 4⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * (n + 2), n * n + 5 * n + 8⟩ := by
  -- Phase 1: d_to_b
  rw [show 2 * (n + 1) = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (e := n * n + 3 * n + 4) (d := 0) (2 * n + 2) 0)
  rw [show 0 + (2 * n + 2) = (2 * n) + 2 from by ring]
  -- Phase 2: opening R5,R1,R3
  step fm; step fm; step fm
  -- State: (2, 2+2*n, 0, 2, n*n+3*n+2)
  rw [show 2 * n + 2 = 2 + 2 * n from by ring,
      show n * n + 3 * n + 2 = (n * n + 2 * n + 2) + n from by ring]
  -- Phase 3: inner loop
  apply stepStar_trans (inner_loop n 0 2 (n * n + 2 * n + 2))
  -- State: (0, 0, n+2, 2+2+2*n, n*n+2*n+2)
  rw [show 0 + n + 2 = 0 + (n + 2) from by ring,
      show 2 + 2 + 2 * n = 2 * (n + 2) from by ring,
      show n * n + 2 * n + 2 = (n * n + n) + (n + 2) from by ring]
  -- Phase 4: c_drain with k = n+2
  apply stepStar_trans (c_drain (D := 2 * (n + 2)) (n + 2) 0 (n * n + n))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 4⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * (n + 1), n * n + 3 * n + 4⟩) 0
  intro n; refine ⟨n + 1, ?_⟩
  have h := main_trans n
  rw [show 2 * (n + 2) = 2 * (n + 1 + 1) from by ring,
      show n * n + 5 * n + 8 = (n + 1) * (n + 1) + 3 * (n + 1) + 4 from by ring] at h
  exact h

end Sz22_2003_unofficial_605
