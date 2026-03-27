import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #278: [14/15, 33/7, 1/3, 125/2, 1/55, 3/5]

Vector representation:
```
 1 -1 -1  1  0
 0  1  0 -1  1
 0 -1  0  0  0
-1  0  3  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_278

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: convert a to c
theorem a_to_c : ∀ k a c, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+3*k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c; simp; exists 0
  | succ k ih =>
    intro a c
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 3))
    ring_nf; finish

-- R5 repeated: cancel c and e
theorem ce_cancel : ∀ k c, ⟨0, 0, c+k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro c; exists 0
  | succ k ih =>
    intro c
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    exact ih c

-- R1+R2 chain: each pair transfers 1 from c to a and e
theorem r1r2_chain : ∀ k a e, ⟨a, 1, k+1, 0, e⟩ [fm]⊢* ⟨a+k+1, 1, 0, 0, e+k+1⟩ := by
  intro k; induction k with
  | zero =>
    intro a e; step fm; step fm; finish
  | succ k ih =>
    intro a e
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- Main cycle: (n+1, 0, 0, 0, n+1) →⁺ (2*n+1, 0, 0, 0, 2*n+1)
theorem main_cycle : ⟨n+1, 0, 0, 0, n+1⟩ [fm]⊢⁺ ⟨2*n+1, 0, 0, 0, 2*n+1⟩ := by
  -- Phase 1: R4 x (n+1): (n+1, 0, 0, 0, n+1) ->* (0, 0, 3*(n+1), 0, n+1)
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (a_to_c (n + 1) 0 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5 x (n+1): (0, 0, 3*(n+1), 0, n+1) ->* (0, 0, 2*(n+1), 0, 0)
  rw [show 3 * (n + 1) = 2 * (n + 1) + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (ce_cancel (n + 1) (2 * (n + 1)))
  -- Phase 3: R6: (0, 0, 2*(n+1), 0, 0) -> (0, 1, 2*(n+1)-1, 0, 0)
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
  step fm
  -- Phase 4: R1+R2 chain
  rw [show 2 * n + 1 = (2 * n) + 1 from by ring]
  apply stepStar_trans (r1r2_chain (2 * n) 0 0)
  simp only [Nat.zero_add]
  -- Phase 5: R3
  step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩)
  · execute fm 7
  apply progress_nonhalt_simple (A := ℕ) (C := fun n ↦ (⟨n+2, 0, 0, 0, n+2⟩ : Q)) (i₀ := 0)
  intro n
  exact ⟨2 * n + 1, by show _ [fm]⊢⁺ _; convert main_cycle (n := n + 1) using 1⟩
