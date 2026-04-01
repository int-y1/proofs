import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1334: [63/10, 2/33, 1331/2, 5/7, 15/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  3
 0  0  1 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1334

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

def E : ℕ → ℕ
  | 0 => 3
  | d + 1 => E d + d + 2

-- R4 chain: move d to c
theorem r4_chain : ∀ d, ⟨0, 0, c, d, e⟩ [fm]⊢* ⟨0, 0, c + d, 0, e⟩ := by
  intro d; induction' d with d ih generalizing c
  · exists 0
  · rw [show c + (d + 1) = (c + 1) + d from by ring]
    step fm
    exact ih (c := c + 1)

-- R3 chain: drain a, adding 3 to e per step
theorem r3_chain : ∀ a, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 3 * a⟩ := by
  intro a; induction' a with a ih generalizing e
  · exists 0
  · step fm
    apply stepStar_trans (ih (e := e + 3))
    ring_nf; finish

-- R2 chain
theorem r2_chain : ∀ k a b e, ⟨a, b + k, 0, d, e + k⟩ [fm]⊢* ⟨a + k, b, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    show ⟨a, (b + k) + 1, 0, d, (e + k) + 1⟩ [fm]⊢* ⟨a + (k + 1), b, 0, d, e⟩
    step fm
    show ⟨a + 1, b + k, 0, d, e + k⟩ [fm]⊢* ⟨a + (k + 1), b, 0, d, e⟩
    rw [show a + (k + 1) = (a + 1) + k from by ring]
    exact ih (a + 1) b e

-- Spiral
theorem spiral : ∀ n k e, ⟨1, k, c + n, k, e + n⟩ [fm]⊢* ⟨1, k + n, c, k + n, e⟩ := by
  intro n; induction n with
  | zero => intro k e; exists 0
  | succ n ih =>
    intro k e
    show ⟨1, k, (c + n) + 1, k, (e + n) + 1⟩ [fm]⊢* ⟨1, k + (n + 1), c, k + (n + 1), e⟩
    step fm
    show ⟨0, k + 2, c + n, k + 1, (e + n) + 1⟩ [fm]⊢* ⟨1, k + (n + 1), c, k + (n + 1), e⟩
    step fm
    show ⟨1, k + 1, c + n, k + 1, e + n⟩ [fm]⊢* ⟨1, k + (n + 1), c, k + (n + 1), e⟩
    rw [show k + (n + 1) = (k + 1) + n from by ring]
    exact ih (k + 1) e

-- E is always ≥ 3
theorem E_ge_3 : ∀ d, E d ≥ 3 := by
  intro d; induction d with
  | zero => simp [E]
  | succ d ih => simp [E]; omega

-- Full transition including R5+R2 opening and all phases
-- (0, 0, d+2, 0, E d+2d+5) →⁺ (0, 0, 0, d+3, E d+3d+9)
theorem opening_and_phases (d : ℕ) :
    ⟨0, 0, d + 2, 0, E d + 2 * d + 5⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 3, E d + 3 * d + 9⟩ := by
  -- R5: need e ≥ 1 (E d+2d+5 ≥ 3+0+5 = 8 ≥ 1)
  rw [show E d + 2 * d + 5 = (E d + 2 * d + 4) + 1 from by ring,
      show d + 2 = (d + 2) from rfl]
  step fm  -- R5: (0, 1, d+3, 0, E d+2d+4)
  -- After R5 the goal is ⊢*
  show ⟨0, 1, (d + 2) + 1, 0, E d + 2 * d + 4⟩ [fm]⊢* ⟨0, 0, 0, d + 3, E d + 3 * d + 9⟩
  rw [show (d + 2) + 1 = d + 3 from by ring,
      show E d + 2 * d + 4 = (E d + 2 * d + 3) + 1 from by ring]
  -- R2: (0, 1, d+3, 0, (E d+2d+3)+1) → (1, 0, d+3, 0, E d+2d+3)
  step fm
  show ⟨1, 0, d + 3, 0, E d + 2 * d + 3⟩ [fm]⊢* ⟨0, 0, 0, d + 3, E d + 3 * d + 9⟩
  -- Phase 3: Spiral (d+3 rounds)
  apply stepStar_trans
  · show ⟨1, 0, d + 3, 0, E d + 2 * d + 3⟩ [fm]⊢* ⟨1, d + 3, 0, d + 3, E d + d⟩
    rw [show d + 3 = 0 + (d + 3) from by ring,
        show E d + 2 * d + 3 = (E d + d) + (d + 3) from by ring]
    exact spiral (d + 3) 0 (E d + d) (c := 0)
  -- After spiral: (1, d+3, 0, d+3, E d+d)
  -- Phase 4: R2 drain (d+3 steps)
  apply stepStar_trans
  · show ⟨1, d + 3, 0, d + 3, E d + d⟩ [fm]⊢* ⟨d + 4, 0, 0, d + 3, E d - 3⟩
    have hE := E_ge_3 d
    rw [show d + 3 = 0 + (d + 3) from by ring,
        show E d + d = (E d - 3) + (d + 3) from by omega,
        show d + 4 = 1 + (d + 3) from by ring]
    exact r2_chain (d + 3) 1 0 (E d - 3)
  -- Phase 5: R3 chain (d+4 steps)
  apply stepStar_trans (r3_chain (d + 4) (d := d + 3) (e := E d - 3))
  have hE := E_ge_3 d
  rw [show E d - 3 + 3 * (d + 4) = E d + 3 * d + 9 from by omega]
  finish

-- General transition for d+2
theorem trans_general (d : ℕ) :
    ⟨0, 0, 0, d + 2, E (d + 2)⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 3, E (d + 3)⟩ := by
  have hE2 : E (d + 2) = E d + 2 * d + 5 := by simp [E]; ring
  have hE3 : E (d + 3) = E d + 3 * d + 9 := by simp [E]; ring
  rw [hE2, hE3]
  -- Phase 1: R4 chain
  apply stepStar_stepPlus_stepPlus
  · exact r4_chain (d + 2) (c := 0) (e := E d + 2 * d + 5)
  show ⟨0, 0, 0 + (d + 2), 0, E d + 2 * d + 5⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 3, E d + 3 * d + 9⟩
  rw [show 0 + (d + 2) = d + 2 from by ring]
  exact opening_and_phases d

-- Transition for d = 0
theorem trans_d0 : ⟨0, 0, 0, 0, E 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, E 1⟩ := by
  show ⟨0, 0, 0, 0, 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, 5⟩
  execute fm 7

-- Transition for d = 1
theorem trans_d1 : ⟨0, 0, 0, 1, E 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2, E 2⟩ := by
  show ⟨0, 0, 0, 1, 5⟩ [fm]⊢⁺ ⟨0, 0, 0, 2, 8⟩
  execute fm 12

-- Main transition
theorem main_trans (d : ℕ) :
    ⟨0, 0, 0, d, E d⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 1, E (d + 1)⟩ := by
  rcases d with _ | _ | d
  · exact trans_d0
  · exact trans_d1
  · exact trans_general d

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, E 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d, E d⟩) 0
  intro d; exists d + 1; exact main_trans d
