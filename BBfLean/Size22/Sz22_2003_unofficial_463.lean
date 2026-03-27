import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #463: [28/15, 21/22, 175/2, 11/7, 2/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  1 -1
-1  0  2  1  0
 0  0  0 -1  1
 1  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_463

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R2/R1 chain: k rounds of (R2, R1)
-- From (a+1, 0, c+k, d, e+k): R2 gives (a, 1, c+k, d+1, e+k-1),
-- then R1 gives (a+2, 0, c+k-1, d+2, e+k-1).
-- Net per round: a+1, c-1, d+2, e-1.
theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a+1, 0, c+k, d, e+k⟩ [fm]⊢* ⟨a+k+1, 0, c, d+2*k, e⟩ := by
  intro k; induction k with
  | zero => intro a c d e; exists 0
  | succ k ih =>
    intro a c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih _ _ _ _); ring_nf; finish

-- R2 drain: k steps of R2, transferring from a and e to b and d
-- From (a+1, b, 0, d, e+1): R2 gives (a, b+1, 0, d+1, e).
theorem r2_drain : ∀ k, ∀ a b d,
    ⟨a+k, b, 0, d, k⟩ [fm]⊢* ⟨a, b+k, 0, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = (k) + 1 from rfl]
    step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish

-- R3 chain: convert a to c and d
theorem r3_chain : ∀ k, ∀ c d,
    ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c+2*k, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

-- R4 drain: transfer d to e
theorem r4_drain : ∀ k, ∀ c e,
    ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c, 0, e+k⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

-- Middle phase: (A+1, B, 0, D, 0) ->* (0, 0, 2A+3B+2, D+A+3B+1, 0)
theorem middle_phase : ∀ B, ∀ A D,
    ⟨A+1, B, 0, D, 0⟩ [fm]⊢* ⟨0, 0, 2*A+3*B+2, D+A+3*B+1, 0⟩ := by
  intro B; induction B using Nat.strongRecOn with
  | ind B ih =>
    intro A D
    match B with
    | 0 =>
      apply stepStar_trans (r3_chain (A+1) 0 D); ring_nf; finish
    | 1 =>
      step fm; step fm; step fm
      apply stepStar_trans (r3_chain (A+1) 3 (D+3)); ring_nf; finish
    | B' + 2 =>
      step fm; step fm; step fm
      rw [show A + 3 + 1 = (A + 3) + 1 from by ring]
      apply stepStar_trans (ih B' (by omega) (A + 3) (D + 3)); ring_nf; finish

-- Main transition with parameters n, f where f <= n
theorem main_trans (n f : ℕ) (hf : f ≤ n) :
    ⟨0, 0, n+2, 0, n+f+1⟩ [fm]⊢⁺ ⟨0, 0, 2*n+f+4, 0, 3*n+3*f+4⟩ := by
  -- Phase 1: R5
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  -- Now at (1, 0, n+1, 0, n+f+1) and goal is ⊢*
  -- Phase 2: R2/R1 chain with n+1 rounds
  rw [show n + 1 = 0 + (n + 1) from by ring,
      show n + f + 1 = f + (n + 1) from by ring]
  apply stepStar_trans (r2r1_chain (n + 1) 0 0 0 f)
  -- Now at (n+2, 0, 0, 2*(n+1), f)
  -- Phase 3: R2 drain with f rounds
  rw [show 0 + (n + 1) + 1 = (n + 2 - f) + f from by omega,
      show 0 + 2 * (n + 1) = 2 * (n + 1) from by ring]
  apply stepStar_trans (r2_drain f (n + 2 - f) 0 (2 * (n + 1)))
  -- Now at (n+2-f, f, 0, 2*(n+1)+f, 0)
  -- Phase 4: middle phase
  rw [show n + 2 - f = (n + 1 - f) + 1 from by omega,
      show 0 + f = f from by ring]
  apply stepStar_trans (middle_phase f (n + 1 - f) (2 * (n + 1) + f))
  -- Phase 5: R4 drain
  rw [show 2 * (n + 1 - f) + 3 * f + 2 = 2 * n + f + 4 from by omega,
      show 2 * (n + 1) + f + (n + 1 - f) + 3 * f + 1 = 3 * n + 3 * f + 4 from by omega]
  apply stepStar_trans (r4_drain (3 * n + 3 * f + 4) (2 * n + f + 4) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 4⟩)
  · execute fm 11
  · apply progress_nonhalt (fm := fm)
      (P := fun q ↦ ∃ n f, q = ⟨0, 0, n+2, 0, n+f+1⟩ ∧ f ≤ n)
    · intro c ⟨n, f, hq, hf⟩; subst hq
      exact ⟨⟨0, 0, 2*n+f+4, 0, 3*n+3*f+4⟩,
             ⟨2*n+f+2, n+2*f+1, by ring_nf, by omega⟩,
             main_trans n f hf⟩
    · exact ⟨2, 1, rfl, by omega⟩
