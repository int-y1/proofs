import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #903: [4/15, 3/14, 275/2, 7/11, 242/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0  0  1 -1
 1  0 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_903

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R4 chain: move e to d.
theorem e_to_d : ∀ k p q d, ⟨0, 0, p, d, q + k⟩ [fm]⊢* ⟨0, 0, p, d + k, q⟩ := by
  intro k; induction' k with k ih <;> intro p q d
  · exists 0
  · rw [show q + (k + 1) = (q + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih p q (d + 1))
    ring_nf; finish

-- R3 chain: convert a to c and e.
theorem r3_chain : ∀ k a p q, ⟨a + k, 0, p, 0, q⟩ [fm]⊢* ⟨a, 0, p + 2 * k, 0, q + k⟩ := by
  intro k; induction' k with k ih <;> intro a p q
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (p + 2) (q + 1))
    ring_nf; finish

-- Spiral: R2+R1 interleaved.
theorem spiral : ∀ k a c d, ⟨a + 1, 0, c + k, d + k, 2⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, 2⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show c + k + 1 = (c + k) + 1 from by ring]
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c d)
    ring_nf; finish

-- Combined phase: (1, 0, c+D, D, 2) →* (0, 0, c+2*D+2, D+3, 0)
theorem combined_phase (c D : ℕ) :
    ⟨1, 0, c + D, D, 2⟩ [fm]⊢* ⟨0, 0, c + 2 * D + 2, D + 3, 0⟩ := by
  have h1 := spiral D 0 c 0
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show D + 1 = 0 + (D + 1) from by ring]
  apply stepStar_trans (r3_chain (D + 1) 0 c 2)
  rw [show c + 2 * (D + 1) = c + 2 * D + 2 from by ring,
      show 2 + (D + 1) = 0 + (D + 3) from by ring]
  apply stepStar_trans (e_to_d (D + 3) (c + 2 * D + 2) 0 0)
  ring_nf; finish

-- Main transition: (0, 0, R+D+2, D, 0) →⁺ (0, 0, R+2D+3, D+3, 0)
theorem main_trans (R D : ℕ) :
    ⟨0, 0, R + D + 2, D, 0⟩ [fm]⊢⁺ ⟨0, 0, R + 2 * D + 3, D + 3, 0⟩ := by
  rw [show R + D + 2 = (R + D + 1) + 1 from by ring]
  step fm
  rw [show R + D + 1 = (R + 1) + D from by ring]
  apply stepStar_trans (combined_phase (R + 1) D)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 9, 7, 0⟩)
  · execute fm 32
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ C D, q = ⟨0, 0, C, D, 0⟩ ∧ C ≥ D + 2 ∧ C ≥ 4)
  · intro c ⟨C, D, hq, hCD, hC4⟩; subst hq
    obtain ⟨R, rfl⟩ : ∃ R, C = R + D + 2 := ⟨C - D - 2, by omega⟩
    refine ⟨⟨0, 0, R + 2 * D + 3, D + 3, 0⟩,
      ⟨R + 2 * D + 3, D + 3, rfl, by omega, by omega⟩,
      main_trans R D⟩
  · exact ⟨9, 7, rfl, by omega, by omega⟩
