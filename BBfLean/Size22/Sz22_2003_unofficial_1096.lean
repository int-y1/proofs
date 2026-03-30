import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1096: [5/6, 343/2, 44/35, 9/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  3  0
 2  0 -1 -1  1
 0  2  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1096

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move e to b. (0, b, 0, d, e+k) →* (0, b+2k, 0, d, e).
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

-- R3,R1,R1 chain: (0, 2k, c+1, d+k, e) →* (0, 0, c+k+1, d, e+k).
theorem r3r1r1_chain : ∀ k, ⟨0, 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c := c + 1) (e := e + 1))
    ring_nf; finish

-- R3,R2,R2 chain: (0, 0, k+1, d+1, e) →* (0, 0, 0, d+5k+6, e+k+1).
theorem r3r2r2_full : ∀ k, ∀ d e, ⟨0, 0, k + 1, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 5 * k + 6, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · step fm; step fm; step fm; finish
  · step fm; step fm; step fm
    rw [show d + 6 = (d + 5) + 1 from by ring]
    apply stepStar_trans (ih (d + 5) (e + 1))
    ring_nf; finish

-- Canonical form: (0, 0, 0, 4e+7, e+1). Transition: e ↦ 2e+2.
theorem main_transition (e : ℕ) : ⟨0, 0, 0, 4 * e + 7, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 8 * e + 15, 2 * e + 3⟩ := by
  rw [show (e + 1 : ℕ) = 0 + (e + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (e + 1) (b := 0) (d := 4 * e + 7) (e := 0))
  rw [show 0 + 2 * (e + 1) = 2 * (e + 1) from by ring,
      show (4 * e + 7 : ℕ) = (4 * e + 6) + 1 from by ring]
  step fm
  rw [show (4 * e + 6 : ℕ) = (3 * e + 5) + (e + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain (e + 1) (c := 0) (d := 3 * e + 5) (e := 0))
  rw [show 0 + (e + 1) + 1 = (e + 1) + 1 from by ring,
      show 0 + (e + 1) = e + 1 from by ring,
      show (3 * e + 5 : ℕ) = (3 * e + 4) + 1 from by ring]
  apply stepStar_trans (r3r2r2_full (e + 1) (3 * e + 4) (e + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 7, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨0, 0, 0, 4 * e + 7, e + 1⟩) 0
  intro e; exists (2 * e + 2)
  rw [show 4 * (2 * e + 2) + 7 = 8 * e + 15 from by ring,
      show (2 * e + 2) + 1 = 2 * e + 3 from by ring]
  exact main_transition e
