import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1567: [7/45, 242/5, 25/77, 3/11, 55/2]

Vector representation:
```
 0 -2 -1  1  0
 1  0 -1  0  2
 0  0  2 -1 -1
 0  1  0  0 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1567

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 chain: transfer e to b (c=0, d=0).
theorem e_to_b : ∀ k, ∀ a b e, ⟨a, b, 0, 0, e + k⟩ [fm]⊢* ⟨a, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a b e; exists 0
  · intro a b e; rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih a (b + 1) e); ring_nf; finish

-- Drain round: 5 steps.
theorem drain_round : ∀ A B D,
    ⟨A + 1, B + 6, 1, D, 1⟩ [fm]⊢* ⟨A, B, 1, D + 2, 1⟩ := by
  intro A B D
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Drain loop: k rounds.
theorem drain_loop : ∀ k, ∀ A B D,
    ⟨A + k, 6 * k + B, 1, D, 1⟩ [fm]⊢* ⟨A, B, 1, D + 2 * k, 1⟩ := by
  intro k; induction' k with k ih
  · intro A B D; ring_nf; exists 0
  · intro A B D
    rw [show 6 * (k + 1) + B = (6 * k + B) + 6 from by ring,
        show A + (k + 1) = (A + k) + 1 from by omega]
    apply stepStar_trans (drain_round (A + k) (6 * k + B) D)
    apply stepStar_trans (ih A B (D + 2)); ring_nf; finish

-- R3/R2/R2 chain with b=1.
theorem r3r2r2_b1 : ∀ k, ∀ A D E,
    ⟨A, 1, 0, D + k, E + 1⟩ [fm]⊢* ⟨A + 2 * k, 1, 0, D, E + 3 * k + 1⟩ := by
  intro k; induction' k with k ih
  · intro A D E; ring_nf; exists 0
  · intro A D E
    rw [show D + (k + 1) = (D + k) + 1 from by omega]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 2) D (E + 3)); ring_nf; finish

-- R3/R2/R2 chain with b=0.
theorem r3r2r2_b0 : ∀ k, ∀ A D E,
    ⟨A, 0, 0, D + k, E + 1⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, D, E + 3 * k + 1⟩ := by
  intro k; induction' k with k ih
  · intro A D E; ring_nf; exists 0
  · intro A D E
    rw [show D + (k + 1) = (D + k) + 1 from by omega]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 2) D (E + 3)); ring_nf; finish

-- Sub-cycle 1: (A+n+1, 1, 0, 0, 6n+2) ⊢⁺ (A+4n+2, 1, 0, 0, 6n+4)
theorem sc1 (A n : ℕ) :
    ⟨A + n + 1, 1, 0, 0, 6 * n + 2⟩ [fm]⊢⁺ ⟨A + 4 * n + 2, 1, 0, 0, 6 * n + 4⟩ := by
  rw [show (6 : ℕ) * n + 2 = 0 + (6 * n + 2) from by omega]
  apply stepStar_stepPlus_stepPlus (e_to_b (6 * n + 2) (A + n + 1) 1 0)
  rw [show 1 + (6 * n + 2) = 6 * n + 3 from by omega]
  -- R5
  step fm
  -- Drain
  apply stepStar_trans (drain_loop n A 3 0)
  -- After drain: (A, 3, 1, 0+2*n, 1), need to massage
  rw [show 0 + 2 * n = 2 * n from by omega]
  -- R1: (A, 3, 1, 2n, 1) -> (A, 1, 0, 2n+1, 1)
  step fm
  -- R3/R2/R2 chain: need (A, 1, 0, 0+(2n+1), 0+1)
  rw [show 2 * n + 1 = 0 + (2 * n + 1) from by omega]
  apply stepStar_trans (r3r2r2_b1 (2 * n + 1) A 0 0)
  ring_nf; finish

-- Sub-cycle 2: (A+4n+2, 1, 0, 0, 6n+4) ⊢⁺ (A+7n+4, 1, 0, 0, 6n+5)
theorem sc2 (A n : ℕ) :
    ⟨A + 4 * n + 2, 1, 0, 0, 6 * n + 4⟩ [fm]⊢⁺ ⟨A + 7 * n + 4, 1, 0, 0, 6 * n + 5⟩ := by
  rw [show (6 : ℕ) * n + 4 = 0 + (6 * n + 4) from by omega]
  apply stepStar_stepPlus_stepPlus (e_to_b (6 * n + 4) (A + 4 * n + 2) 1 0)
  rw [show 1 + (6 * n + 4) = 6 * n + 5 from by omega]
  -- R5
  step fm
  -- Drain
  rw [show A + 4 * n + 1 = (A + 3 * n + 1) + n from by omega]
  apply stepStar_trans (drain_loop n (A + 3 * n + 1) 5 0)
  rw [show 0 + 2 * n = 2 * n from by omega]
  -- R1, R3, R1: (A+3n+1, 5, 1, 2n, 1) -> (A+3n+1, 1, 1, 2n+1, 0)
  step fm; step fm; step fm
  -- R2: (A+3n+1, 1, 1, 2n+1, 0) -> (A+3n+2, 1, 0, 2n+1, 2)
  step fm
  -- R3/R2/R2 chain
  rw [show 2 * n + 1 = 0 + (2 * n + 1) from by omega,
      show (2 : ℕ) = 1 + 1 from by omega]
  apply stepStar_trans (r3r2r2_b1 (2 * n + 1) (A + 3 * n + 2) 0 1)
  ring_nf; finish

-- Sub-cycle 3: (A+7n+4, 1, 0, 0, 6n+5) ⊢⁺ (A+10n+7, 1, 0, 0, 6n+8)
theorem sc3 (A n : ℕ) :
    ⟨A + 7 * n + 4, 1, 0, 0, 6 * n + 5⟩ [fm]⊢⁺ ⟨A + 10 * n + 7, 1, 0, 0, 6 * n + 8⟩ := by
  rw [show (6 : ℕ) * n + 5 = 0 + (6 * n + 5) from by omega]
  apply stepStar_stepPlus_stepPlus (e_to_b (6 * n + 5) (A + 7 * n + 4) 1 0)
  rw [show 1 + (6 * n + 5) = 6 * n + 6 from by omega]
  -- R5
  step fm
  -- Drain
  rw [show A + 7 * n + 3 = (A + 6 * n + 3) + n from by omega]
  apply stepStar_trans (drain_loop n (A + 6 * n + 3) 6 0)
  rw [show 0 + 2 * n = 2 * n from by omega]
  -- After drain: (A+6n+3, 6, 1, 2n, 1)
  -- R1: (A+6n+3, 4, 0, 2n+1, 1)
  -- R3: (A+6n+3, 4, 2, 2n, 0)
  -- R1: (A+6n+3, 2, 1, 2n+1, 0)
  -- R1: (A+6n+3, 0, 0, 2n+2, 0)
  step fm; step fm; step fm; step fm
  -- R5: (A+6n+2, 0, 1, 2n+2, 1)
  step fm
  -- R2: (A+6n+3, 0, 0, 2n+2, 3)
  step fm
  -- R3/R2/R2 chain with b=0
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by omega,
      show (3 : ℕ) = 2 + 1 from by omega]
  apply stepStar_trans (r3r2r2_b0 (2 * n + 2) (A + 6 * n + 3) 0 2)
  -- Result: (A+6n+3+2(2n+2), 0, 0, 0, 2+3(2n+2)+1) = (A+10n+7, 0, 0, 0, 6n+9)
  -- R4: one step
  rw [show A + 6 * n + 3 + 2 * (2 * n + 2) = A + 10 * n + 7 from by ring,
      show 2 + 3 * (2 * n + 2) + 1 = (6 * n + 8) + 1 from by ring]
  step fm; finish

-- Main transition.
theorem main_trans (A n : ℕ) :
    ⟨A + n + 1, 1, 0, 0, 6 * n + 2⟩ [fm]⊢⁺ ⟨A + 10 * n + 7, 1, 0, 0, 6 * n + 8⟩ :=
  stepPlus_trans (stepPlus_trans (sc1 A n) (sc2 A n)) (sc3 A n)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 1, 0, 0, 2⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, n⟩ ↦ ⟨A + n + 1, 1, 0, 0, 6 * n + 2⟩) ⟨0, 0⟩
  intro ⟨A, n⟩; exact ⟨⟨A + 9 * n + 5, n + 1⟩, by
    show (A + n + 1, 1, 0, 0, 6 * n + 2) [fm]⊢⁺ (A + 9 * n + 5 + (n + 1) + 1, 1, 0, 0, 6 * (n + 1) + 2)
    rw [show A + 9 * n + 5 + (n + 1) + 1 = A + 10 * n + 7 from by ring,
        show 6 * (n + 1) + 2 = 6 * n + 8 from by ring]
    exact main_trans A n⟩

end Sz22_2003_unofficial_1567
