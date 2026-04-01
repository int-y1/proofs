import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1427: [7/15, 22/3, 117/77, 5/13, 507/2]

Vector representation:
```
 0 -1 -1  1  0  0
 1 -1  0  0  1  0
 0  2  0 -1 -1  1
 0  0  1  0  0 -1
-1  1  0  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1427

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a, b+2, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+2⟩
  | _ => none

-- R4 chain: transfer f to c.
theorem f_to_c : ∀ k c f, ⟨a, (0 : ℕ), c, 0, e, f + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c f
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c + 1) f); ring_nf; finish

-- Interleaved R1/R3 chain.
theorem r1r3_chain : ∀ E, E ≥ 1 → ∀ A D F,
    ⟨A, (2 : ℕ), 2 * E + 1, D, E, F⟩ [fm]⊢* ⟨A + 1, 0, 0, D + E + 1, 1, F + E⟩ := by
  intro E; induction' E with E ih
  · omega
  · intro hE A D F
    rcases E with _ | E
    · -- E+1 = 1
      rw [show 2 * (0 + 1) + 1 = (1 : ℕ) + 1 + 1 from by ring]
      step fm; step fm; step fm; step fm; step fm
      ring_nf; finish
    · -- E+2 >= 2
      rw [show 2 * (E + 1 + 1) + 1 = (2 * (E + 1) + 1) + 1 + 1 from by ring]
      step fm; step fm; step fm
      apply stepStar_trans (ih (by omega) A (D + 1) (F + 1))
      ring_nf; finish

-- R3-R2-R2 chain.
theorem r3r2r2_chain : ∀ k, ∀ A D E F,
    ⟨A, (0 : ℕ), 0, D + k, E + 1, F⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, D, E + 1 + k, F + k⟩ := by
  intro k; induction' k with k ih <;> intro A D E F
  · exists 0
  · rw [show D + (k + 1) = (D + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 2) D (E + 1) (F + 1))
    ring_nf; finish

-- Main transition: (e*e+1, 0, 0, 0, e+1, 2*e+2) ⊢⁺ (e*e+2*e+2+1, 0, 0, 0, e+2, 2*e+4)
-- Using n = e+1 as the canonical parameter:
-- Canonical state for parameter n >= 1: (n*n - n + 1, 0, 0, 0, n, 2*n)
-- For n = e+1: a = (e+1)^2 - (e+1) + 1 = e^2 + e + 1
-- Next: n = e+2: a = (e+2)^2 - (e+2) + 1 = e^2 + 3e + 3
-- So transition: (e*e+e+1, 0, 0, 0, e+1, 2*e+2) ⊢⁺ (e*e+3*e+3, 0, 0, 0, e+2, 2*e+4)
theorem main_trans (e : ℕ) :
    ⟨e * e + e + 1, (0 : ℕ), 0, 0, e + 1, 2 * e + 2⟩ [fm]⊢⁺
    ⟨e * e + 3 * e + 3, 0, 0, 0, e + 2, 2 * e + 4⟩ := by
  -- Phase 1: f_to_c: transfer f=2e+2 to c
  rw [show 2 * e + 2 = 0 + (2 * e + 2) from by ring]
  apply stepStar_stepPlus_stepPlus
    (f_to_c (2 * e + 2) 0 0 (a := e * e + e + 1) (e := e + 1))
  rw [show (0 : ℕ) + (2 * e + 2) = 2 * (e + 1) from by ring]
  -- State: (e*e+e+1, 0, 2*(e+1), 0, e+1, 0)
  -- Phase 2: R5
  rw [show e * e + e + 1 = (e * e + e) + 1 from by ring]
  step fm
  -- State: (e*e+e, 1, 2*(e+1), 0, e+1, 2)
  -- Phase 3: R1, R3, then r1r3_chain
  rw [show 2 * (e + 1) = (2 * e + 1) + 1 from by ring]
  step fm  -- R1
  -- State: (e*e+e, 0, 2*e+1, 1, e+1, 2)
  rw [show (e + 1 : ℕ) = e + 1 from rfl]
  step fm  -- R3: needs d=1>=1, e+1>=1
  -- State: (e*e+e, 2, 2*e+1, 0, e, 3)
  rcases e with _ | e
  · -- e = 0, so original e+1 = 1
    -- State: (0, 2, 1, 0, 0, 3)
    step fm; step fm  -- R1, R2
    -- State: (1, 0, 0, 1, 1, 3)
    step fm; step fm; step fm  -- R3, R2, R2
    ring_nf; finish
  · -- e >= 1
    -- State: ((e+1)*(e+1)+(e+1), 2, 2*(e+1)+1, 0, e+1, 3)
    rw [show 2 * (e + 1) + 1 = 2 * (e + 1) + 1 from rfl]
    apply stepStar_trans (r1r3_chain (e + 1) (by omega) ((e + 1) * (e + 1) + (e + 1)) 0 3)
    -- State: ((e+1)*(e+1)+(e+1)+1, 0, 0, e+2, 1, e+4)
    rw [show 0 + (e + 1) + 1 = 0 + (e + 2) from by ring,
        show 3 + (e + 1) = e + 4 from by ring]
    apply stepStar_trans (r3r2r2_chain (e + 2)
      ((e + 1) * (e + 1) + (e + 1) + 1) 0 0 (e + 4))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1, 2⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨e * e + e + 1, 0, 0, 0, e + 1, 2 * e + 2⟩) 0
  intro e
  refine ⟨e + 1, ?_⟩
  have h := main_trans e
  rw [show e * e + 3 * e + 3 = (e + 1) * (e + 1) + (e + 1) + 1 from by ring,
      show e + 2 = e + 1 + 1 from by ring,
      show 2 * e + 4 = 2 * (e + 1) + 2 from by ring] at h
  exact h

end Sz22_2003_unofficial_1427
