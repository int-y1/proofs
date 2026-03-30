import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1150: [5/6, 44/35, 5929/2, 3/11, 2/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  2
 0  1  0  0 -1
 1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1150

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 chain: move e to b (a=0, c=0)
theorem e_to_b : ∀ k b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R3 chain: drain a (b=0, c=0)
theorem r3_drain : ∀ A d e, ⟨A, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * A, e + 2 * A⟩ := by
  intro A; induction' A with A ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 2) (e + 2))
    ring_nf; finish

-- Interleave chain: R2+R1+R1 repeated k times
-- From (0, 2k+1, C+1, k+D+1, E) to (0, 1, C+k+1, D+1, E+k)
theorem interleave : ∀ k C D E,
    ⟨0, 2 * k + 1, C + 1, k + D + 1, E⟩ [fm]⊢* ⟨0, 1, C + k + 1, D + 1, E + k⟩ := by
  intro k; induction' k with k ih <;> intro C D E
  · ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring,
        show (k + 1) + D + 1 = (k + D + 1) + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    step fm  -- R1
    rw [show C + 2 = (C + 1) + 1 from by ring]
    apply stepStar_trans (ih (C + 1) D (E + 1))
    ring_nf; finish

-- c_drain: (A, 0, C, 2, E) →* (0, 0, 0, 2A+3C+2, E+2A+5C)
theorem c_drain : ∀ C A E,
    ⟨A, 0, C, 2, E⟩ [fm]⊢* ⟨0, 0, 0, 2 * A + 3 * C + 2, E + 2 * A + 5 * C⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih_strong; intro A E
  rcases C with _ | _ | C
  · apply stepStar_trans (r3_drain A 2 E)
    ring_nf; finish
  · step fm  -- R2: (A+2, 0, 0, 1, E+1)
    step fm  -- R3: (A+1, 0, 0, 3, E+3)
    apply stepStar_trans (r3_drain (A + 1) 3 (E + 3))
    ring_nf; finish
  · rw [show (C + 2 : ℕ) = C + 1 + 1 from by ring]
    step fm  -- R2: (A+2, 0, C+1, 1, E+1)
    step fm  -- R2: (A+4, 0, C, 0, E+2)
    step fm  -- R3: (A+3, 0, C, 2, E+4)
    apply stepStar_trans (ih_strong C (by omega) (A + 3) (E + 4))
    ring_nf; finish

-- Full transition: (0,0,0,n+2,2n+2) ⊢⁺ (0,0,0,3n+5,6n+8)
-- Phase structure:
--   R4 drain → R5 → R1 → interleave → R2 → R1 → R3 → c_drain
theorem full_transition (n : ℕ) :
    ⟨0, 0, 0, n + 2, 2 * n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * n + 5, 6 * n + 8⟩ := by
  -- First R4 step (gives ⊢⁺)
  rw [show (2 * n + 2 : ℕ) = (2 * n + 1) + 1 from by ring]
  step fm  -- R4: (0, 1, 0, n+2, 2n+1)
  -- Remaining R4 steps
  rw [show (2 * n + 1 : ℕ) = 0 + (2 * n + 1) from by ring]
  apply stepStar_trans (e_to_b (2 * n + 1) 1 (n + 2) 0)
  -- Now at (0, 1+(2n+1), 0, n+2, 0) = (0, 2n+2, 0, n+2, 0)
  -- R5
  rw [show 1 + (2 * n + 1) = 2 * n + 2 from by ring,
      show (n + 2 : ℕ) = (n + 1) + 1 from by ring]
  step fm  -- R5: (1, 2n+2, 0, n+1, 0)
  -- R1
  rw [show (2 * n + 2 : ℕ) = (2 * n + 1) + 1 from by ring]
  step fm  -- R1: (0, 2n+1, 1, n+1, 0)
  -- Interleave
  rw [show (n + 1 : ℕ) = n + 0 + 1 from by ring]
  apply stepStar_trans (interleave n 0 0 0)
  -- Now at (0, 1, n+1, 1, n)
  rw [show 0 + n + 1 = n + 1 from by ring,
      show (0 + 1 : ℕ) = 1 from by ring,
      show (0 + n : ℕ) = n from by ring]
  -- R2: (0, 1, n+1, 1, n) → (2, 1, n, 0, n+1)
  rw [show (n + 1 : ℕ) = n + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- R1: (2, 1, n, 0, n+1) → (1, 0, n+1, 0, n+1)
  step fm
  -- R3: (1, 0, n+1, 0, n+1) → (0, 0, n+1, 2, n+3)
  step fm
  -- c_drain
  apply stepStar_trans (c_drain (n + 1) 0 (n + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, 2 * n + 2⟩) 0
  intro n
  refine ⟨3 * n + 3, ?_⟩
  show ⟨0, 0, 0, n + 2, 2 * n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * n + 3 + 2, 2 * (3 * n + 3) + 2⟩
  have h := full_transition n
  convert h using 2; ring_nf
