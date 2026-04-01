import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1182: [5/6, 49/2, 44/35, 9/11, 15/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  2  0  0 -1
 0  1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1182

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 repeated: transfer e to b. Each step: e-=1, b+=2.
theorem e_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

-- Interleave: (R3, R1, R1) repeated j times.
-- From (0, 2j+1, k+1, D+j, E) to (0, 1, k+j+1, D, E+j).
theorem interleave : ∀ j, ∀ k D E,
    ⟨0, 2 * j + 1, k + 1, D + j, E⟩ [fm]⊢* ⟨0, 1, k + j + 1, D, E + j⟩ := by
  intro j; induction' j with j ih <;> intro k D E
  · exists 0
  · rw [show 2 * (j + 1) + 1 = (2 * j + 1 + 1) + 1 from by ring,
        show D + (j + 1) = (D + j) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih (k + 1) D (E + 1))
    ring_nf; finish

-- Last interleave step + R2: (0, 1, c+1, D+1, E) ⊢* (0, 0, c+1, D+2, E+1)
theorem last_interleave : ⟨0, 1, c + 1, D + 1, E⟩ [fm]⊢* ⟨0, 0, c + 1, D + 2, E + 1⟩ := by
  step fm
  step fm
  step fm
  ring_nf; finish

-- Drain: (R3, R2, R2) repeated k times.
-- From (0, 0, c+k, D+1, E) to (0, 0, c, D+3*k+1, E+k).
theorem drain : ∀ k, ∀ c D E,
    ⟨0, 0, c + k, D + 1, E⟩ [fm]⊢* ⟨0, 0, c, D + 3 * k + 1, E + k⟩ := by
  intro k; induction' k with k ih <;> intro c D E
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show D + 2 + 2 = (D + 3) + 1 from by ring]
    apply stepStar_trans (ih c (D + 3) (E + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, D+e+2, e) ⊢⁺ (0, 0, 0, D+3e+5, 2e+2)
theorem main_transition (D e : ℕ) :
    ⟨0, 0, 0, D + e + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, D + 3 * e + 5, 2 * e + 2⟩ := by
  -- Phase 1: drain e via R4
  have h1 := e_to_b e 0 (D + e + 2) 0
  rw [show (0 : ℕ) + e = e from by ring, show 0 + 2 * e = 2 * e from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: R5
  rw [show D + e + 2 = (D + e + 1) + 1 from by ring]
  step fm
  -- Phase 3: interleave e rounds
  have h3 := interleave e 0 (D + 1) 0
  rw [show 2 * e + 1 = 2 * e + 1 from by ring,
      show (0 : ℕ) + 1 = 1 from by ring,
      show (D + 1) + e = D + e + 1 from by ring,
      show 0 + e + 1 = e + 1 from by ring,
      show 0 + e = e from by ring] at h3
  apply stepStar_trans h3
  -- Phase 4: last interleave + R2
  apply stepStar_trans (last_interleave (c := e) (D := D) (E := e))
  -- Phase 5: drain (e+1) rounds
  have h5 := drain (e + 1) 0 (D + 1) (e + 1)
  rw [show (0 : ℕ) + (e + 1) = e + 1 from by ring,
      show (D + 1) + 1 = D + 2 from by ring,
      show (D + 1) + 3 * (e + 1) + 1 = D + 3 * e + 5 from by ring,
      show e + 1 + (e + 1) = 2 * e + 2 from by ring] at h5
  exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨D, e⟩ ↦ ⟨0, 0, 0, D + e + 2, e⟩) ⟨0, 0⟩
  intro ⟨D, e⟩
  exists ⟨D + e + 1, 2 * e + 2⟩
  show ⟨0, 0, 0, D + e + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, (D + e + 1) + (2 * e + 2) + 2, 2 * e + 2⟩
  rw [show (D + e + 1) + (2 * e + 2) + 2 = D + 3 * e + 5 from by ring]
  exact main_transition D e

end Sz22_2003_unofficial_1182
