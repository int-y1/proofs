import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #545: [28/15, 9/7, 1/6, 625/2, 3/5]

Vector representation:
```
 2 -1 -1  1
 0  2  0 -1
-1 -1  0  0
-1  0  4  0
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_545

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+4, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4 repeated: convert a to c (when b=0, d=0)
theorem a_to_c : ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+4*k, 0⟩ := by
  have many_step : ∀ k c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+4*k, 0⟩ := by
    intro k; induction' k with k h <;> intro c
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k c

-- R2 repeated: convert d to b
theorem d_to_b : ⟨a, b, 0, d+k⟩ [fm]⊢* ⟨a, b+2*k, 0, d⟩ := by
  have many_step : ∀ k b d, ⟨a, b, 0, d+k⟩ [fm]⊢* ⟨a, b+2*k, 0, d⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b d

-- R3 repeated: annihilate a and b together
theorem r3_chain : ⟨a+k, k, 0, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  have many_step : ∀ k a, ⟨a+k, k, 0, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
    intro k; induction' k with k h <;> intro a
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k a

-- Core interleaving: R2,R1,R1 rounds
-- From (a, 0, 2*(k+1), d+1): R2 -> (a,2,2*(k+1),d) -> R1 -> (a+2,1,2*k+1,d+1) -> R1 -> (a+4,0,2*k,d+2)
-- After induction: (a, 0, 2*(k+1), d+1) ->* (a+4*(k+1), 0, 0, d+k+2)
theorem r2r1r1_chain : ⟨a, 0, 2*(k+1), d+1⟩ [fm]⊢* ⟨a+4*(k+1), 0, 0, d+k+2⟩ := by
  have many_step : ∀ k a d, ⟨a, 0, 2*(k+1), d+1⟩ [fm]⊢* ⟨a+4*(k+1), 0, 0, d+k+2⟩ := by
    intro k; induction' k with k h <;> intro a d
    · step fm; step fm; step fm; finish
    rw [show 2 * (k + 1 + 1) = (2 * (k + 1) + 1) + 1 from by ring]
    step fm
    rw [show (2 * (k + 1) + 1 : ℕ) = (2 * (k + 1)) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a d

-- Opening: (0, 0, 4n+4, 0) ->⁺ (6, 0, 4n, 2) via R5,R1,R2,R1,R1
theorem opening : ⟨0, 0, 4*n+4, 0⟩ [fm]⊢⁺ ⟨6, 0, 4*n, 2⟩ := by
  rw [show 4 * n + 4 = (4 * n + 3) + 1 from by ring]
  step fm
  rw [show (4 * n + 3 : ℕ) = (4 * n + 2) + 1 from by ring]
  step fm; step fm
  rw [show (4 * n + 2 : ℕ) = (4 * n + 1) + 1 from by ring]
  step fm
  rw [show (4 * n + 1 : ℕ) = 4 * n + 1 from rfl]
  step fm; ring_nf; finish

-- Closing n=0: (6, 0, 0, 2) ->* (2, 0, 0, 0)
theorem closing_zero : ⟨6, 0, 0, 2⟩ [fm]⊢* ⟨2, 0, 0, 0⟩ := by
  apply stepStar_trans (d_to_b (a := 6) (b := 0) (d := 0) (k := 2))
  rw [show (6 : ℕ) = 2 + 4 from by ring]
  apply stepStar_trans (r3_chain (a := 2) (k := 4))
  finish

-- Closing n>=1: (6, 0, 4*(n'+1), 2) ->* (4*n'+6, 0, 0, 0)
theorem closing_succ : ⟨6, 0, 4*(n'+1), 2⟩ [fm]⊢* ⟨4*n'+6, 0, 0, 0⟩ := by
  -- r2r1r1_chain needs form (a, 0, 2*(k+1), d+1)
  -- 4*(n'+1) = 2*((2*n'+1)+1), d=2=1+1
  have h1 : (⟨6, 0, 4*(n'+1), 2⟩ : Q) = ⟨6, 0, 2*((2*n'+1)+1), 1+1⟩ := by ring_nf
  rw [h1]
  apply stepStar_trans (r2r1r1_chain (a := 6) (k := 2*n'+1) (d := 1))
  -- State: (6+4*(2*n'+2), 0, 0, 1+(2*n'+1)+2) = (8*n'+14, 0, 0, 2*n'+4)
  have h2 : (⟨6 + 4*((2*n'+1)+1), 0, 0, 1+(2*n'+1)+2⟩ : Q) =
             ⟨(4*n'+6)+(4*n'+8), 0, 0, 0+(2*n'+4)⟩ := by ring_nf
  rw [h2]
  apply stepStar_trans (d_to_b (a := (4*n'+6)+(4*n'+8)) (b := 0) (d := 0) (k := 2*n'+4))
  have h3 : (⟨(4*n'+6)+(4*n'+8), 0+2*(2*n'+4), 0, 0⟩ : Q) =
             ⟨(4*n'+6)+(4*n'+8), 4*n'+8, 0, 0⟩ := by ring_nf
  rw [h3]
  apply stepStar_trans (r3_chain (a := 4*n'+6) (k := 4*n'+8))
  finish

-- Full transition: (n+1, 0, 0, 0) ->+ (4n+2, 0, 0, 0)
theorem main_trans : ⟨n+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨4*n+2, 0, 0, 0⟩ := by
  -- Phase 1: R4 chain: (n+1, 0, 0, 0) ->* (0, 0, 4n+4, 0)
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (a_to_c (a := 0) (k := n + 1) (c := 0))
  simp only [Nat.zero_add]
  -- Goal: (0, 0, 4*(n+1), 0) ⊢⁺ (4*n+2, 0, 0, 0)
  -- Phase 2: opening gives ⊢⁺ to (6, 0, 4n, 2)
  rcases n with _ | n'
  · -- n=0: (0, 0, 4, 0) ⊢⁺ (2, 0, 0, 0)
    apply stepPlus_stepStar_stepPlus (opening (n := 0))
    exact closing_zero
  · -- n=n'+1: (0, 0, 4n'+8, 0) ⊢⁺ (4n'+6, 0, 0, 0)
    rw [show 4 * (n' + 1) + 2 = 4 * n' + 6 from by ring]
    apply stepPlus_stepStar_stepPlus (opening (n := n' + 1))
    exact closing_succ

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0⟩) 0
  intro n; exists 4 * n + 4
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show 4 * n + 4 + 2 = 4 * (n + 1) + 2 from by ring]
  exact main_trans
