import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #95: [1/30, 21/2, 4/77, 5/7, 9317/3]

Vector representation:
```
-1 -1 -1  0  0
-1  1  0  1  0
 2  0  0 -1 -1
 0  0  1 -1  0
 0 -1  0  1  3
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_95

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e+3⟩
  | _ => none

-- Phase A: k rounds of (R5, R3, R1, R1)
-- (0, b+3k, c+2k, 0, e) →* (0, b, c, 0, e+2k)
theorem phaseA : ⟨0, b + 3 * k, c + 2 * k, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e + 2 * k⟩ := by
  have h : ∀ k b c e, ⟨0, b + 3 * k, c + 2 * k, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e + 2 * k⟩ := by
    intro k; induction k with
    | zero => intro b c e; simp; exists 0
    | succ k ih =>
      intro b c e
      rw [show b + 3 * (k + 1) = (b + 3 * k + 2) + 1 from by ring,
          show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring]
      step fm
      rw [show (e + 3 : ℕ) = (e + 2) + 1 from by ring]
      step fm
      rw [show (b + 3 * k + 2 : ℕ) = (b + 3 * k + 1) + 1 from by ring,
          show (c + 2 * k + 1 : ℕ) = (c + 2 * k) + 1 from by ring]
      step fm
      rw [show (b + 3 * k + 1 : ℕ) = (b + 3 * k) + 1 from by ring]
      step fm
      apply stepStar_trans (ih b c (e + 2)); ring_nf; finish
  exact h k b c e

-- Phase B: (0, bb+1, 1, 0, e) →* (2, bb, 0, 0, e+1)
-- Case bb=0: R5, R3, R2, R1, R3
-- Case bb≥1: R5, R3, R1, R2, R3
theorem phaseB : ⟨0, bb + 1, 1, 0, e⟩ [fm]⊢* ⟨2, bb, 0, 0, e + 1⟩ := by
  rcases bb with _ | bb
  · -- bb = 0: (0, 1, 1, 0, e)
    rw [show (0 : ℕ) + 1 = 0 + 1 from by ring]
    step fm  -- R5: (0, 0, 1, 1, e+3)
    rw [show (e + 3 : ℕ) = (e + 2) + 1 from by ring]
    step fm  -- R3: (2, 0, 1, 0, e+2)
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm  -- R2: (1, 1, 1, 1, e+2)
    step fm  -- R1: (0, 0, 0, 1, e+2)
    rw [show (e + 2 : ℕ) = (e + 1) + 1 from by ring]
    step fm  -- R3: (2, 0, 0, 0, e+1)
    finish
  · -- bb = bb+1: (0, bb+2, 1, 0, e)
    rw [show (bb + 1) + 1 = (bb + 1) + 1 from by ring]
    step fm  -- R5: (0, bb+1, 1, 1, e+3)
    rw [show (e + 3 : ℕ) = (e + 2) + 1 from by ring]
    step fm  -- R3: (2, bb+1, 1, 0, e+2)
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show (bb + 1 : ℕ) = bb + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm  -- R1: (1, bb, 0, 0, e+2)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm  -- R2: (0, bb+1, 0, 1, e+2)
    rw [show (e + 2 : ℕ) = (e + 1) + 1 from by ring]
    step fm  -- R3: (2, bb+1, 0, 0, e+1)
    finish

-- R3-R2-R2 chain: k rounds
-- (0, X, 0, D+1, E+k) →* (0, X+2k, 0, D+1+k, E)
theorem r3r2r2_chain :
    ⟨0, X, 0, D + 1, E + k⟩ [fm]⊢* ⟨0, X + 2 * k, 0, D + 1 + k, E⟩ := by
  have h : ∀ k X D E,
      ⟨0, X, 0, D + 1, E + k⟩ [fm]⊢* ⟨0, X + 2 * k, 0, D + 1 + k, E⟩ := by
    intro k; induction k with
    | zero => intro X D E; simp; exists 0
    | succ k ih =>
      intro X D E
      rw [show E + (k + 1) = (E + k) + 1 from by ring]
      step fm  -- R3: (2, X, 0, D, E+k)
      rw [show (2 : ℕ) = 1 + 1 from by ring]
      step fm  -- R2: (1, X+1, 0, D+1, E+k)
      rw [show (1 : ℕ) = 0 + 1 from by ring]
      step fm  -- R2: (0, X+2, 0, D+2, E+k)
      apply stepStar_trans (ih (X + 2) (D + 1) E); ring_nf; finish
  exact h k X D E

-- Phase C: (2, B, 0, 0, E+1) →* (0, B+2E+4, 0, E+3, 0)
theorem phaseC : ⟨2, B, 0, 0, E + 1⟩ [fm]⊢* ⟨0, B + 2 * E + 4, 0, E + 3, 0⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm  -- R2: (1, B+1, 0, 1, E+1)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm  -- R2: (0, B+2, 0, 2, E+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show E + 1 = 0 + (E + 1) from by ring]
  apply stepStar_trans
    (r3r2r2_chain (X := B + 2) (D := 1) (E := 0) (k := E + 1))
  ring_nf; finish

-- Phase D: R4 chain, k rounds
-- (0, X, c, d+k, 0) →* (0, X, c+k, d, 0)
theorem phaseD : ⟨0, X, c, d + k, 0⟩ [fm]⊢* ⟨0, X, c + k, d, 0⟩ := by
  have h : ∀ k c d, ⟨0, X, c, d + k, 0⟩ [fm]⊢* ⟨0, X, c + k, d, 0⟩ := by
    intro k; induction k with
    | zero => intro c d; simp; exists 0
    | succ k ih =>
      intro c d
      rw [show d + (k + 1) = (d + k) + 1 from by ring]
      step fm  -- R4
      apply stepStar_trans (ih (c + 1) d); ring_nf; finish
  exact h k c d

-- Main transition: (0, bb+3n+1, 2n+1, 0, 0) →⁺ (0, bb+4n+4, 2n+3, 0, 0)
-- which is C(bb, n) →⁺ C(bb+n, n+1) where C(bb,n) = (0, bb+3n+1, 2n+1, 0, 0)
theorem main_trans (bb n : ℕ) :
    ⟨0, bb + 3 * n + 1, 2 * n + 1, 0, 0⟩ [fm]⊢⁺
    ⟨0, bb + 4 * n + 4, 2 * n + 3, 0, 0⟩ := by
  -- Phase A: n rounds → (0, bb+1, 1, 0, 2n)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, bb + 1, 1, 0, 2 * n⟩)
  · convert phaseA (b := bb + 1) (c := 1) (k := n) (e := 0) using 2
    all_goals ring_nf
  -- Phase B: (0, bb+1, 1, 0, 2n) → (2, bb, 0, 0, 2n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, bb, 0, 0, 2 * n + 1⟩)
  · exact phaseB (bb := bb) (e := 2 * n)
  -- Phase C: (2, bb, 0, 0, 2n+1) → (0, bb+4n+4, 0, 2n+3, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, bb + 4 * n + 4, 0, 2 * n + 3, 0⟩)
  · convert phaseC (B := bb) (E := 2 * n) using 2
    all_goals ring_nf
  -- Phase D: (0, bb+4n+4, 0, 2n+3, 0) → (0, bb+4n+4, 2n+3, 0, 0)
  apply step_stepStar_stepPlus
  · -- First R4 step
    rw [show (2 * n + 3 : ℕ) = (2 * n + 2) + 1 from by ring]
    show fm ⟨0, bb + 4 * n + 4, 0, (2 * n + 2) + 1, 0⟩ =
      some ⟨0, bb + 4 * n + 4, 1, 2 * n + 2, 0⟩
    simp [fm]
  -- Remaining D steps: (0, bb+4n+4, 1, 2n+2, 0) →* (0, bb+4n+4, 2n+3, 0, 0)
  convert phaseD (X := bb + 4 * n + 4) (c := 1) (d := 0) (k := 2 * n + 2) using 2
  all_goals ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: (1, 0, 0, 0, 0) →* (0, 1, 1, 0, 0) = C(0, 0) in 2 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 1, 0, 0⟩) (by execute fm 2)
  -- C(bb, n) = (0, bb+3n+1, 2n+1, 0, 0), start with bb=0, n=0: (0, 1, 1, 0, 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨bb, n⟩ ↦ ⟨0, bb + 3 * n + 1, 2 * n + 1, 0, 0⟩) ⟨0, 0⟩
  intro ⟨bb, n⟩; exact ⟨⟨bb + n, n + 1⟩, by convert main_trans bb n using 2; all_goals ring_nf⟩

end Sz22_2003_unofficial_95
