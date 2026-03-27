import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #450: [28/15, 1/3, 33/2, 25/11, 1/35, 3/5]

Vector representation:
```
 2 -1 -1  1  0
 0 -1  0  0  0
-1  1  0  0  1
 0  0  2  0 -1
 0  0 -1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_450

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1/R3 interleaved chain
theorem r1r3_chain : ∀ k, ∀ a d e, ⟨a, 1, k, d, e⟩ [fm]⊢* ⟨a+k, 1, 0, d+k, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show a + (k + 1) = (a + 1) + k from by ring,
      show d + (k + 1) = (d + 1) + k from by ring,
      show e + (k + 1) = (e + 1) + k from by ring]
  step fm; step fm
  exact ih _ _ _

-- R3/R2 drain of a register
theorem r3r2_drain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih d (e + 1))
  ring_nf; finish

-- R4 chain: e -> c
theorem r4_chain : ∀ k, ∀ c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (ih (c + 2) d)
  ring_nf; finish

-- R5 chain: c and d drain together
theorem r5_chain : ∀ k, ∀ c, ⟨0, 0, c+k, k, 0⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  exact ih _

-- Full cycle: (0, 0, n+2, 0, 0) ⊢* (0, 0, 3*n+3, 0, 0)
theorem cycle (n : ℕ) : ⟨0, 1, n+1, 0, 0⟩ [fm]⊢* ⟨0, 0, 3*n+3, 0, 0⟩ := by
  -- R1/R3 chain: (0, 1, n+1, 0, 0) ->* (n+1, 1, 0, n+1, n+1)
  apply stepStar_trans (r1r3_chain (n+1) 0 0 0)
  simp only [Nat.zero_add]
  -- R2: (n+1, 1, 0, n+1, n+1) -> (n+1, 0, 0, n+1, n+1)
  step fm
  -- R3/R2 drain: (n+1, 0, 0, n+1, n+1) ->* (0, 0, 0, n+1, 2*(n+1))
  apply stepStar_trans (r3r2_drain (n+1) (n+1) (n+1))
  rw [show n + 1 + (n + 1) = 2 * (n + 1) from by ring]
  -- R4 chain: (0, 0, 0, n+1, 2*(n+1)) ->* (0, 0, 4*(n+1), n+1, 0)
  apply stepStar_trans (r4_chain (2*(n+1)) 0 (n+1))
  simp only [Nat.zero_add]
  -- R5 chain
  rw [show 2 * (2 * (n + 1)) = 3 * n + 3 + (n + 1) from by ring]
  exact r5_chain (n+1) (3*n+3)

-- Main transition
theorem main_trans (n : ℕ) : ⟨0, 0, n+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3*n+3, 0, 0⟩ := by
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  exact cycle n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n+2, 0, 0⟩) 0
  intro n; exact ⟨3*n+1, main_trans n⟩
