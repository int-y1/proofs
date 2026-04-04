import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1774: [9/10, 275/21, 4/3, 7/11, 33/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  2 -1  1
 2 -1  0  0  0
 0  0  0  1 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1774

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R3 chain: (a, b+k, 0, 0, e) →* (a+2*k, b, 0, 0, e)
theorem r3_chain : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (b := b))
    ring_nf; finish

-- R4 chain: (a, 0, 0, d, e+k) →* (a, 0, 0, d+k, e)
theorem r4_chain : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e))
    ring_nf; finish

-- Spiral: k rounds of (R2, R1, R1).
-- (a+2*k+1, 3*j+1, 0, k, j+1) →* (a+1, 3*(j+k)+1, 0, 0, j+k+1)
theorem spiral : ∀ k, ⟨a + 2 * k + 1, 3 * j + 1, 0, k, j + 1⟩ [fm]⊢*
    ⟨a + 1, 3 * (j + k) + 1, 0, 0, j + k + 1⟩ := by
  intro k; induction' k with k ih generalizing a j
  · exists 0
  · rw [show a + 2 * (k + 1) + 1 = (a + 2 * k + 1) + 2 from by ring,
        show j + 1 = 0 + j + 1 from by ring]
    step fm
    rw [show 0 + j + 1 + 1 = j + 2 from by ring]
    step fm; step fm
    rw [show 3 * j + 4 = 3 * (j + 1) + 1 from by ring,
        show j + 2 = (j + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a) (j := j + 1))
    ring_nf; finish

-- Main transition: (a+2*d+2, 0, 0, d, 0) →⁺ (a+6*d+3, 0, 0, d+1, 0)
theorem main_trans : ⟨a + 2 * d + 2, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 6 * d + 3, 0, 0, d + 1, 0⟩ := by
  -- R5
  step fm
  -- Spiral
  rw [show (1 : ℕ) = 3 * 0 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (spiral d (a := a) (j := 0))
  rw [show 0 + d = d from by ring]
  -- R3 chain
  rw [show 3 * d + 1 = 0 + (3 * d + 1) from by ring]
  apply stepStar_trans (r3_chain (3 * d + 1) (a := a + 1) (b := 0) (e := d + 1))
  rw [show a + 1 + 2 * (3 * d + 1) = a + 6 * d + 3 from by ring]
  -- R4 chain
  rw [show d + 1 = 0 + (d + 1) from by ring]
  exact r4_chain (d + 1) (a := a + 6 * d + 3) (d := 0) (e := 0)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 2, 0⟩)
  · execute fm 13
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A d, q = ⟨A, 0, 0, d, 0⟩ ∧ A ≥ 2 * d + 2 ∧ d ≥ 1)
  · intro c ⟨A, d, hq, hA, hd⟩; subst hq
    obtain ⟨a, rfl⟩ : ∃ a, A = a + 2 * d + 2 := ⟨A - (2 * d + 2), by omega⟩
    exact ⟨⟨a + 6 * d + 3, 0, 0, d + 1, 0⟩,
      ⟨a + 6 * d + 3, d + 1, rfl, by omega, by omega⟩, main_trans⟩
  · exact ⟨7, 2, rfl, by omega, by omega⟩
