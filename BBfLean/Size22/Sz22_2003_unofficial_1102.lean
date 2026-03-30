import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1102: [5/6, 4/245, 3773/2, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -2  0
-1  0  0  3  1
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1102

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+2, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move e to b.
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R2+R1+R1 interleaved chain.
-- Each round: R2 (c+1,d+2→a+2), R1 (a+1,b+1→c+1), R1 again.
theorem interleave : ∀ k, ∀ b c d, ⟨0, b + 2 * k, c + 1, d + 2 * k, 0⟩ [fm]⊢* ⟨0, b, c + k + 1, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + 2 * (k + 1) = b + 2 * k + 2 from by ring,
        show d + 2 * (k + 1) = d + 2 * k + 2 from by ring]
    show ⟨0, b + 2 * k + 2, (c + 1), (d + 2 * k) + 2, 0⟩ [fm]⊢* _
    step fm
    show ⟨0 + 2, b + 2 * k + 2, c, d + 2 * k, 0⟩ [fm]⊢* _
    rw [show (0 : ℕ) + 2 = 1 + 1 from by ring,
        show b + 2 * k + 2 = (b + 2 * k + 1) + 1 from by ring]
    step fm
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih b (c + 1) d)
    ring_nf; finish

-- Tail: R2+R1. From (0, 1, n+1, d+2, 0) to (1, 0, n+1, d, 0).
theorem tail : ⟨0, 1, n + 1, d + 2, 0⟩ [fm]⊢* ⟨1, 0, n + 1, d, 0⟩ := by
  step fm; step fm; finish

-- Drain: R2 repeated. Each step consumes 1 c and 2 d, gives 2 a.
theorem drain : ∀ k, ∀ a c d, ⟨a, 0, c + k, d + 2 * k, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    show ⟨a, 0, (c + k) + 1, (d + 2 * k) + 2, 0⟩ [fm]⊢* _
    step fm
    show ⟨a + 2, 0, c + k, d + 2 * k, 0⟩ [fm]⊢* _
    apply stepStar_trans (ih (a + 2) c d)
    ring_nf; finish

-- R3 chain: each step converts 1 a to 3 d and 1 e.
theorem r3_chain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (d + 3) (e + 1))
    ring_nf; finish

-- Full transition from canonical n to canonical n+1.
-- C(n) = (0, 0, 0, n*n+3*n+3, 2*n+1).
-- We prove C(n) ⊢⁺ C(n+1), but only for n ≥ 2 to avoid special cases in drain.
-- Bootstrap handles n=0,1 by execute.
theorem full_trans (n : ℕ) :
    ⟨0, 0, 0, (n + 2) * (n + 2) + 3 * (n + 2) + 3, 2 * (n + 2) + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, (n + 3) * (n + 3) + 3 * (n + 3) + 3, 2 * (n + 3) + 1⟩ := by
  -- Simplify the expressions
  rw [show (n + 2) * (n + 2) + 3 * (n + 2) + 3 = n * n + 7 * n + 13 from by ring,
      show 2 * (n + 2) + 1 = 2 * n + 5 from by ring,
      show (n + 3) * (n + 3) + 3 * (n + 3) + 3 = n * n + 9 * n + 21 from by ring,
      show 2 * (n + 3) + 1 = 2 * n + 7 from by ring]
  -- Phase 1: First R4 step for ⊢⁺
  rw [show (2 * n + 5 : ℕ) = 2 * n + 4 + 1 from by ring]
  step fm
  -- Remaining R4 steps
  rw [show (2 * n + 4 : ℕ) = 0 + (2 * n + 4) from by ring]
  apply stepStar_trans (e_to_b (2 * n + 4) (b := 1) (d := n * n + 7 * n + 13) (e := 0))
  -- Now at (0, 2n+5, 0, D, 0). R5 step.
  rw [show 1 + (2 * n + 4) = 2 * n + 5 from by ring,
      show n * n + 7 * n + 13 = (n * n + 7 * n + 12) + 1 from by ring]
  apply stepStar_trans
  · show ⟨0, 2 * n + 5, 0, (n * n + 7 * n + 12) + 1, 0⟩ [fm]⊢* ⟨0, 2 * n + 5, 1, n * n + 7 * n + 12, 0⟩
    execute fm 1
  -- Now at (0, 2n+5, 1, n²+7n+12, 0). Interleave with k=n+2 rounds.
  rw [show 2 * n + 5 = 1 + 2 * (n + 2) from by ring,
      show n * n + 7 * n + 12 = (n * n + 5 * n + 8) + 2 * (n + 2) from by ring]
  apply stepStar_trans (interleave (n + 2) 1 0 (n * n + 5 * n + 8))
  -- Now at (0, 1, n+3, n²+5n+8, 0).
  rw [show 0 + (n + 2) + 1 = n + 3 from by ring,
      show n * n + 5 * n + 8 = (n * n + 5 * n + 6) + 2 from by ring]
  -- Tail: R2+R1
  apply stepStar_trans (tail (n := n + 2) (d := n * n + 5 * n + 6))
  -- Now at (1, 0, n+3, n²+5n+6, 0).
  rw [show n + 2 + 1 = n + 3 from by ring]
  -- Drain: n+3 steps of R2
  rw [show (n + 3 : ℕ) = 0 + (n + 3) from by ring,
      show n * n + 5 * n + 6 = (n * n + 3 * n) + 2 * (n + 3) from by ring]
  apply stepStar_trans (drain (n + 3) 1 0 (n * n + 3 * n))
  -- Now at (2n+7, 0, 0, n²+3n, 0).
  rw [show 1 + 2 * (n + 3) = 2 * n + 7 from by ring]
  -- R3 chain: 2n+7 steps
  apply stepStar_trans (r3_chain (2 * n + 7) (n * n + 3 * n) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 13, 5⟩) (by execute fm 25)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, (n + 2) * (n + 2) + 3 * (n + 2) + 3, 2 * (n + 2) + 1⟩) 0
  intro n; exists (n + 1)
  show ⟨0, 0, 0, (n + 2) * (n + 2) + 3 * (n + 2) + 3, 2 * (n + 2) + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, ((n + 1) + 2) * ((n + 1) + 2) + 3 * ((n + 1) + 2) + 3, 2 * ((n + 1) + 2) + 1⟩
  rw [show (n + 1) + 2 = n + 3 from by ring]
  exact full_trans n

end Sz22_2003_unofficial_1102
