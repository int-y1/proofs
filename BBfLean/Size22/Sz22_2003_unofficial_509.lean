import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #509: [28/15, 3/22, 5/2, 11/7, 308/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  1  0  0
 0  0  0 -1  1
 2  0 -1  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_509

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e+1⟩
  | _ => none

-- R3 repeated: convert a to c
theorem a_to_c : ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  have many_step : ∀ k c, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
    intro k; induction' k with k h <;> intro c
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k c

-- R4 repeated: convert d to e (a=0, so R3 doesn't fire)
theorem d_to_e : ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  have many_step : ∀ k d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k d e

-- R2+R1 chain: each round does R2 then R1
theorem r2r1_chain : ⟨a+2, 0, k, d, e+k⟩ [fm]⊢* ⟨a+k+2, 0, 0, d+k, e⟩ := by
  have many_step : ∀ k a d, ⟨a+2, 0, k, d, e+k⟩ [fm]⊢* ⟨a+k+2, 0, 0, d+k, e⟩ := by
    intro k; induction' k with k h <;> intro a d
    · exists 0
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a d

-- R2 repeated: drain e into b
theorem e_to_b : ⟨a+k, b, 0, d, k⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
  have many_step : ∀ k a b, ⟨a+k, b, 0, d, k⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
    intro k; induction' k with k h <;> intro a b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a b

-- R3+R1 chain: (a+1, k, 0, d, 0) ->* (a+k+1, 0, 0, d+k, 0)
theorem r3r1_chain : ⟨a+1, k, 0, d, 0⟩ [fm]⊢* ⟨a+k+1, 0, 0, d+k, 0⟩ := by
  have many_step : ∀ k a d, ⟨a+1, k, 0, d, 0⟩ [fm]⊢* ⟨a+k+1, 0, 0, d+k, 0⟩ := by
    intro k; induction' k with k h <;> intro a d
    · exists 0
    rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a d

-- Main transition: (n+2, 0, 0, 2n+2, 0) ->+ (n+3, 0, 0, 2n+4, 0)
theorem main_trans : ⟨n+2, 0, 0, 2*n+2, 0⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 2*n+4, 0⟩ := by
  -- Phase 1: R3 x (n+2): (n+2, 0, 0, 2n+2, 0) ->* (0, 0, n+2, 2n+2, 0)
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (a_to_c (a := 0) (k := n + 2) (c := 0) (d := 2 * n + 2))
  simp only [Nat.zero_add]
  -- Phase 2: R4 x (2n+2): (0, 0, n+2, 2n+2, 0) ->* (0, 0, n+2, 0, 2n+2)
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (c := n + 2) (d := 0) (k := 2 * n + 2) (e := 0))
  simp only [Nat.zero_add]
  -- Phase 3a: R5 step: (0, 0, (n+1)+1, 0, 2n+2) -> (2, 0, n+1, 1, 2n+3)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl :
    (⟨0, 0, (n + 1) + 1, 0, 2 * n + 2⟩ : Q) [fm]⊢ ⟨2, 0, n + 1, 1, 2 * n + 3⟩)
  -- Phase 3b: R2+R1 chain: (2, 0, n+1, 1, 2n+3) ->* (n+3, 0, 0, n+2, n+2)
  rw [show (2 : ℕ) = 0 + 2 from by ring, show 2 * n + 3 = (n + 2) + (n + 1) from by ring]
  apply stepStar_trans (r2r1_chain (a := 0) (k := n + 1) (d := 1) (e := n + 2))
  -- State: (0+(n+1)+2, 0, 0, 1+(n+1), n+2) = (n+3, 0, 0, n+2, n+2)
  rw [show 0 + (n + 1) + 2 = 1 + (n + 2) from by ring, show 1 + (n + 1) = n + 2 from by ring]
  -- Phase 4: R2 drain: (1+(n+2), 0, 0, n+2, n+2) ->* (1, n+2, 0, n+2, 0)
  apply stepStar_trans (e_to_b (a := 1) (k := n + 2) (b := 0) (d := n + 2))
  simp only [Nat.zero_add]
  -- Phase 5: R3+R1 chain: (0+1, n+2, 0, n+2, 0) ->* (0+(n+2)+1, 0, 0, (n+2)+(n+2), 0)
  apply stepStar_trans (r3r1_chain (a := 0) (k := n + 2) (d := n + 2))
  rw [show 0 + (n + 2) + 1 = n + 3 from by ring,
      show n + 2 + (n + 2) = 2 * n + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 2 * n + 2, 0⟩) 0
  intro n; exists n + 1
  rw [show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_trans
