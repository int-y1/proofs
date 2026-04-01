import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1333: [63/10, 2/33, 1331/2, 5/7, 14/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  3
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1333

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 chain: move d to c
theorem d_to_c : ∀ k, ∀ c d, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih
  · intro c d; exists 0
  · intro c d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- R1/R2 interleaving
theorem interleave : ∀ n, ∀ b d e, ⟨1, b, n + 1, d, e + n⟩ [fm]⊢* ⟨0, b + n + 2, 0, d + n + 1, e⟩ := by
  intro n; induction' n with n ih
  · intro b d e; step fm; ring_nf; finish
  · intro b d e
    rw [show n + 1 + 1 = (n + 1) + 1 from by ring]
    step fm
    rw [show e + (n + 1) = (e + n) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) (d + 1) e)
    ring_nf; finish

-- R2 drain
theorem r2_drain : ∀ k, ∀ a b e, ⟨a, b + k, 0, d, e + k⟩ [fm]⊢* ⟨a + k, b, 0, d, e⟩ := by
  intro k; induction' k with k ih
  · intro a b e; exists 0
  · intro a b e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b e)
    ring_nf; finish

-- R3 chain
theorem r3_chain : ∀ a, ∀ e, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 3 * a⟩ := by
  intro a; induction' a with a ih
  · intro e; exists 0
  · intro e; step fm
    apply stepStar_trans (ih (e + 3))
    ring_nf; finish

-- Full transition
theorem full_trans : ⟨0, 0, 0, d + 1, e + 2 * d + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2, e + 3 * d + 6⟩ := by
  -- Phase 1: first R4 step (establishes ⊢⁺)
  rw [show d + 1 = 0 + (d + 1) from by ring]
  step fm
  -- After step fm: goal is ⊢* from (0, 0, 1, Nat.add 0 d, e+2d+3)
  -- Remaining R4 steps
  change ⟨0, 0, 1, 0 + d, e + 2 * d + 3⟩ [fm]⊢* ⟨0, 0, 0, d + 2, e + 3 * d + 6⟩
  apply stepStar_trans (d_to_c d 1 0 (e := e + 2 * d + 3))
  rw [show 1 + d = d + 1 from by ring]
  -- R5 step
  rw [show e + 2 * d + 3 = (e + 2 * d + 2) + 1 from by ring]
  step fm
  -- Interleave: (1, 0, d+1, 1, e+2d+2) →* (0, d+2, 0, d+2, e+d+2)
  rw [show e + 2 * d + 2 = (e + d + 2) + d from by ring]
  apply stepStar_trans (interleave d 0 1 (e + d + 2))
  rw [show 0 + d + 2 = 0 + (d + 2) from by ring,
      show 1 + d + 1 = d + 2 from by ring,
      show e + d + 2 = e + (d + 2) from by ring]
  -- R2 drain: (0, d+2, 0, d+2, e+d+2) →* (d+2, 0, 0, d+2, e)
  apply stepStar_trans (r2_drain (d + 2) 0 0 e)
  rw [show 0 + (d + 2) = d + 2 from by ring]
  -- R3 chain: (d+2, 0, 0, d+2, e) →* (0, 0, 0, d+2, e+3*(d+2))
  exact r3_chain (d + 2) e

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 5⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d + 1, e + 2 * d + 3⟩) ⟨0, 2⟩
  intro ⟨d, e⟩
  refine ⟨⟨d + 1, e + d + 1⟩, ?_⟩
  show ⟨0, 0, 0, d + 1, e + 2 * d + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, (d + 1) + 1, (e + d + 1) + 2 * (d + 1) + 3⟩
  rw [show (d + 1) + 1 = d + 2 from by ring,
      show (e + d + 1) + 2 * (d + 1) + 3 = e + 3 * d + 6 from by ring]
  exact full_trans
