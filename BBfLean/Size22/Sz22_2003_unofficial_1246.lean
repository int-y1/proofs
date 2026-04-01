import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1246: [5/6, 77/2, 44/35, 3/121, 15/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 2  0 -1 -1  1
 0  1  0  0 -2
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1246

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 repeated: drain e by pairs. (0, b, 0, d, e+2*k) →* (0, b+k, 0, d, e).
theorem e_drain : ∀ k, ⟨0, b, 0, d, e + 2 * k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (e := e + 2) (b := b))
    step fm
    ring_nf; finish

-- R3+R1+R1 chain. Each round: (0, B+2, C+1, D+1, E) → (0, B, C+2, D, E+1).
-- After k rounds: (0, 2*k+b, c+1, d+k, e) →* (0, b, c+k+1, d, e+k).
theorem r3r1r1_chain : ∀ k, ⟨0, 2 * k + b, c + 1, d + k, e⟩ [fm]⊢* ⟨0, b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · ring_nf; exists 0
  · rw [show 2 * (k + 1) + b = 2 * k + (b + 2) from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b := b + 2) (d := d + 1))
    step fm  -- R3
    step fm  -- R1
    step fm  -- R1
    rw [show c + k + 1 + 1 = c + (k + 1) + 1 from by ring,
        show e + k + 1 = e + (k + 1) from by ring]
    finish

-- Tail: (0, 1, c+1, 1, e) → R3 → R1 → R2 → (0, 0, c+1, 1, e+2).
theorem tail : ⟨0, 1, c + 1, 1, e⟩ [fm]⊢* ⟨0, 0, c + 1, 1, e + 2⟩ := by
  step fm  -- R3: (2, 1, c, 0, e+1)
  step fm  -- R1: (1, 0, c+1, 0, e+1)
  step fm  -- R2: (0, 0, c+1, 1, e+2)
  finish

-- R3+R2+R2 chain. Each round from (0, 0, C+1, D+1, E):
-- R3: (2, 0, C, D, E+1), R2: (1, 0, C, D+1, E+2), R2: (0, 0, C, D+2, E+3).
-- After k rounds: (0, 0, c+k, d+1, e) →* (0, 0, c, d+k+1, e+3*k).
theorem r3r2r2_chain : ∀ k c d e, ⟨0, 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + k + 1, e + 3 * k⟩ := by
  intro k; induction' k with k ih
  · intro c d e; ring_nf; exists 0
  · intro c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm  -- R3: needs c+1, d+1
    step fm  -- R2
    step fm  -- R2
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 3))
    rw [show d + 1 + k + 1 = d + (k + 1) + 1 from by ring,
        show e + 3 + 3 * k = e + 3 * (k + 1) from by ring]
    finish

-- Main transition: (0, 0, 0, n+2, 4*n+5) →⁺ (0, 0, 0, n+3, 4*n+9)
theorem main_trans (n : ℕ) : ⟨0, 0, 0, n + 2, 4 * n + 5⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 3, 4 * n + 9⟩ := by
  -- Phase 1: e_drain. 4*n+5 = 1 + 2*(2*n+2).
  rw [show (4 * n + 5 : ℕ) = 1 + 2 * (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_drain (2 * n + 2) (b := 0) (d := n + 2) (e := 1))
  rw [show (0 : ℕ) + (2 * n + 2) = 2 * n + 2 from by ring]
  -- Now at (0, 2*n+2, 0, n+2, 1). R5 fires.
  step fm  -- R5: (0, 2*n+3, 1, n+2, 0)
  -- Phase 2: r3r1r1_chain for n+1 rounds.
  rw [show (2 * n + 3 : ℕ) = 2 * (n + 1) + 1 from by ring,
      show (n + 2 : ℕ) = 1 + (n + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain (n + 1) (b := 1) (c := 0) (d := 1) (e := 0))
  rw [show 0 + (n + 1) + 1 = n + 2 from by ring,
      show (0 : ℕ) + (n + 1) = n + 1 from by ring]
  -- Now at (0, 1, n+2, 1, n+1). Tail phase.
  rw [show (n + 2 : ℕ) = (n + 1) + 1 from by ring]
  apply stepStar_trans (tail (c := n + 1) (e := n + 1))
  rw [show (n + 1 : ℕ) + 1 = n + 2 from by ring,
      show n + 1 + 2 = n + 3 from by ring]
  -- Now at (0, 0, n+2, 1, n+3). r3r2r2_chain for n+2 rounds.
  rw [show (n + 2 : ℕ) = 0 + (n + 2) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (n + 2) 0 0 (n + 3))
  rw [show 0 + (n + 2) + 1 = n + 3 from by ring,
      show n + 3 + 3 * (n + 2) = 4 * n + 9 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 5⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, 4 * n + 5⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
