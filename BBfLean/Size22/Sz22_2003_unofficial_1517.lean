import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1517: [7/15, 99/14, 4/3, 25/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  1
 2 -1  0  0  0
 0  0  2  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1517

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: convert e to c.
theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (c := c) (e := e + 1))
    step fm
    rw [show c + 2 * k + 2 = c + 2 * (k + 1) from by ring]
    finish

-- Spiral: R1, R2, R1 repeated. 3 steps per round.
theorem spiral : ∀ n, ⟨A + n, 1, 2 * n, D, E⟩ [fm]⊢* ⟨A, 1, 0, D + n, E + n⟩ := by
  intro n; induction' n with n ih generalizing A D E
  · exists 0
  · rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring,
        show A + (n + 1) = A + n + 1 from by ring]
    step fm
    step fm
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    apply stepStar_trans (ih (A := A) (D := D + 1) (E := E + 1))
    ring_nf; finish

-- R2 chain: drain a and d simultaneously when c = 0.
theorem r2_chain : ∀ k, ⟨A + k, B, 0, D + k, E⟩ [fm]⊢* ⟨A, B + 2 * k, 0, D, E + k⟩ := by
  intro k; induction' k with k ih generalizing A B D E
  · exists 0
  · rw [show A + (k + 1) = A + k + 1 from by ring,
        show D + (k + 1) = D + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (A := A) (B := B + 2) (D := D) (E := E + 1))
    ring_nf; finish

-- R3 chain: drain b to a.
theorem r3_chain : ∀ k, ⟨A, B + k, 0, 0, E⟩ [fm]⊢* ⟨A + 2 * k, B, 0, 0, E⟩ := by
  intro k; induction' k with k ih generalizing A B E
  · exists 0
  · rw [show B + (k + 1) = B + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (A := A + 2) (B := B) (E := E))
    ring_nf; finish

-- R3+R2+R2 drain (even): from (0, B+1, 0, 2k, E) to (0, B+3k+1, 0, 0, E+2k).
theorem drain_even : ∀ k, ∀ B E, ⟨0, B + 1, 0, 2 * k, E⟩ [fm]⊢* ⟨0, B + 3 * k + 1, 0, 0, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro B E
  · ring_nf; exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show B + 4 = (B + 3) + 1 from by ring]
    apply stepStar_trans (ih (B + 3) (E + 2))
    ring_nf; finish

-- R3+R2+R2 drain (odd): from (0, B+1, 0, 2k+1, E) to (1, B+3k+2, 0, 0, E+2k+1).
theorem drain_odd : ∀ k, ∀ B E, ⟨0, B + 1, 0, 2 * k + 1, E⟩ [fm]⊢* ⟨1, B + 3 * k + 2, 0, 0, E + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro B E
  · step fm
    step fm
    finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show B + 4 = (B + 3) + 1 from by ring]
    apply stepStar_trans (ih (B + 3) (E + 2))
    ring_nf; finish

-- R2 chain from spiral end: (A+1, 1, 0, D+A+1, D+A+2) ⊢* (0, 2A+3, 0, D, D+2A+3)
theorem spiral_end_r2 (A D : ℕ) :
    ⟨A + 1, 1, 0, D + A + 1, D + A + 2⟩ [fm]⊢* ⟨0, 2 * A + 3, 0, D, D + 2 * A + 3⟩ := by
  rw [show A + 1 = 0 + (A + 1) from by ring,
      show D + A + 1 = D + (A + 1) from by ring]
  apply stepStar_trans (r2_chain (A + 1) (B := 1) (A := 0) (D := D) (E := D + A + 2))
  ring_nf; finish

-- Even drain + R3 chain: from (0, 2A+3, 0, 2K, E) to (4A+6K+6, 0, 0, 0, E+2K)
theorem drain_r3_even (A K E : ℕ) :
    ⟨0, 2 * A + 3, 0, 2 * K, E⟩ [fm]⊢* ⟨4 * A + 6 * K + 6, 0, 0, 0, E + 2 * K⟩ := by
  rw [show 2 * A + 3 = (2 * A + 2) + 1 from by ring]
  apply stepStar_trans (drain_even K (2 * A + 2) E)
  rw [show (2 * A + 2) + 3 * K + 1 = 0 + (2 * A + 3 * K + 3) from by ring]
  apply stepStar_trans (r3_chain (2 * A + 3 * K + 3) (A := 0) (B := 0) (E := E + 2 * K))
  ring_nf; finish

-- Odd drain + R3 chain: from (0, 2A+3, 0, 2K+1, E) to (4A+6K+9, 0, 0, 0, E+2K+1)
theorem drain_r3_odd (A K E : ℕ) :
    ⟨0, 2 * A + 3, 0, 2 * K + 1, E⟩ [fm]⊢* ⟨4 * A + 6 * K + 9, 0, 0, 0, E + 2 * K + 1⟩ := by
  rw [show 2 * A + 3 = (2 * A + 2) + 1 from by ring]
  apply stepStar_trans (drain_odd K (2 * A + 2) E)
  rw [show (2 * A + 2) + 3 * K + 2 = 0 + (2 * A + 3 * K + 4) from by ring]
  apply stepStar_trans (r3_chain (2 * A + 3 * K + 4) (A := 1) (B := 0) (E := E + 2 * K + 1))
  ring_nf; finish

-- Full transition: (d+2a+3, 0, 0, 0, d+a+1) →⁺ (3d+4a+6, 0, 0, 0, 2d+2a+3)
theorem main_transition (a d : ℕ) :
    ⟨d + 2 * a + 3, 0, 0, 0, d + a + 1⟩ [fm]⊢⁺ ⟨3 * d + 4 * a + 6, 0, 0, 0, 2 * d + 2 * a + 3⟩ := by
  -- Phase 1: R4 chain.
  rw [show (d + a + 1 : ℕ) = 0 + (d + a + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (d + a + 1) (a := d + 2 * a + 3) (c := 0) (e := 0))
  rw [show 0 + 2 * (d + a + 1) = 2 * (d + a + 1) from by ring]
  -- Phase 2: R5.
  rw [show d + 2 * a + 3 = (d + 2 * a + 2) + 1 from by ring]
  step fm
  -- Phase 3: Spiral.
  rw [show d + 2 * a + 2 = (a + 1) + (d + a + 1) from by ring,
      show 2 * (d + a + 1) = 2 * (d + a + 1) from rfl]
  apply stepStar_trans (spiral (d + a + 1) (A := a + 1) (D := 0) (E := 1))
  rw [show 0 + (d + a + 1) = d + a + 1 from by ring,
      show 1 + (d + a + 1) = d + a + 2 from by ring]
  -- Phase 4+5: R2 step + R2 chain combined via spiral_end_r2.
  apply stepStar_trans (spiral_end_r2 a d)
  -- Now at (0, 2a+3, 0, d, d+2a+3).
  -- Phase 6: Parity split on d for drain + R3 chain.
  rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK; subst hK
    apply stepStar_trans (drain_r3_even a K (2 * K + 2 * a + 3))
    ring_nf; finish
  · subst hK
    apply stepStar_trans (drain_r3_odd a K (2 * K + 1 + 2 * a + 3))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 3⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨d + 2 * a + 3, 0, 0, 0, d + a + 1⟩) ⟨0, 2⟩
  intro ⟨a, d⟩; exists ⟨d + 2 * a + 1, d + 1⟩
  show ⟨d + 2 * a + 3, 0, 0, 0, d + a + 1⟩ [fm]⊢⁺ ⟨(d + 1) + 2 * (d + 2 * a + 1) + 3, 0, 0, 0, (d + 1) + (d + 2 * a + 1) + 1⟩
  rw [show (d + 1) + 2 * (d + 2 * a + 1) + 3 = 3 * d + 4 * a + 6 from by ring,
      show (d + 1) + (d + 2 * a + 1) + 1 = 2 * d + 2 * a + 3 from by ring]
  exact main_transition a d

end Sz22_2003_unofficial_1517
