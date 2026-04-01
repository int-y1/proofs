import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1513: [7/15, 99/14, 2/3, 5/11, 231/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  1
 1 -1  0  0  0
 0  0  1  0 -1
-1  1  0  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1513

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
  | _ => none

-- R1R1R2 chain: each round does R1, R1, R2 reducing a by 1 and c by 2.
theorem r1r1r2_chain : ∀ k, ∀ D E, ⟨k, 2, 2 * k + 1, D, E⟩ [fm]⊢* ⟨0, 2, 1, D + k, E + k⟩ := by
  intro k; induction' k with k ih <;> intro D E
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih (D + 1) (E + 1)); ring_nf; finish

-- R3R2 chain: drains d, each round does R3 then R2.
theorem r3r2_chain : ∀ k, ∀ B E, ⟨0, B + 1, 0, k, E⟩ [fm]⊢* ⟨0, B + k + 1, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro B E
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (B + 1) (E + 1)); ring_nf; finish

-- R3 drain: transfers b to a.
theorem r3_drain : ∀ k, ∀ A E, ⟨A, k, 0, 0, E⟩ [fm]⊢* ⟨A + k, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  · step fm
    apply stepStar_trans (ih (A + 1) E); ring_nf; finish

-- R4 transfer: transfers e to c.
theorem r4_transfer : ∀ k, ∀ A C, ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · step fm
    apply stepStar_trans (ih A (C + 1)); ring_nf; finish

-- Main transition: (n+2, 0, 2n+2, 0, 0) ⊢⁺ (n+3, 0, 2n+4, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 2 * n + 4, 0, 0⟩ := by
  -- R5: (n+2, 0, 2n+2, 0, 0) -> (n+1, 1, 2n+2, 1, 1)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  -- R1: (n+1, 1, 2n+2, 1, 1) -> (n+1, 0, 2n+1, 2, 1)
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  -- R2: (n+1, 0, 2n+1, 2, 1) -> (n, 2, 2n+1, 1, 2)
  rw [show (n + 1 : ℕ) = n + 1 from rfl,
      show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  -- R1R1R2 chain: (n, 2, 2n+1, 1, 2) -> (0, 2, 1, n+1, n+2)
  apply stepStar_trans (r1r1r2_chain n 1 2)
  -- R1: (0, 2, 1, n+1, n+2) -> (0, 1, 0, n+2, n+2)
  rw [show 1 + n = n + 1 from by ring, show 2 + n = n + 2 from by ring]
  step fm
  -- R3: (0, 1, 0, n+2, n+2) -> (1, 0, 0, n+2, n+2)
  step fm
  -- R2: (1, 0, 0, n+2, n+2) -> (0, 2, 0, n+1, n+3)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  -- R3R2 chain: (0, 2, 0, n+1, n+3) -> (0, n+3, 0, 0, 2n+4)
  apply stepStar_trans (r3r2_chain (n + 1) 1 (n + 3))
  -- R3 drain: (0, n+3, 0, 0, 2n+4) -> (n+3, 0, 0, 0, 2n+4)
  rw [show 1 + (n + 1) + 1 = n + 3 from by ring,
      show n + 3 + (n + 1) = 2 * n + 4 from by ring]
  apply stepStar_trans (r3_drain (n + 3) 0 (2 * n + 4))
  -- R4 transfer: (n+3, 0, 0, 0, 2n+4) -> (n+3, 0, 2n+4, 0, 0)
  rw [show 0 + (n + 3) = n + 3 from by ring]
  apply stepStar_trans (r4_transfer (2 * n + 4) (n + 3) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 0⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 2 * n + 2, 0, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1513
