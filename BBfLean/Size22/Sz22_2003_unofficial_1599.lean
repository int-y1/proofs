import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1599: [77/15, 14/3, 27/22, 5/7, 33/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  1  0
-1  3  0  0 -1
 0  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1599

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: move d to c. (a, 0, c, d+k, 0) ->* (a, 0, c+k, d, 0)
theorem d_to_c : ∀ k, ∀ a c d, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) d)
    ring_nf; finish

-- R3+R1^3 drain chain
theorem drain_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 3 * k, d, e + 1⟩ [fm]⊢*
    ⟨a, 0, 0, d + 3 * k, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 3 * (k + 1) = (3 * k + 2) + 1 from by ring]
    step fm
    rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring]
    step fm
    rw [show 3 * k + 1 = (3 * k) + 1 from by ring]
    step fm
    step fm
    show ⟨a + k, 0, 3 * k, d + 1 + 1 + 1, (e + 1 + 1) + 1⟩ [fm]⊢*
      ⟨a, 0, 0, d + 3 * (k + 1), e + 2 * (k + 1) + 1⟩
    apply stepStar_trans (ih a (d + 3) (e + 2))
    ring_nf; finish

-- R3+R2^3 climb chain
theorem climb : ∀ k, ∀ a d, ⟨a + 1, 0, 0, d, k + 1⟩ [fm]⊢*
    ⟨a + 2 * k + 3, 0, 0, d + 3 * k + 3, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; step fm; step fm; finish
  · step fm; step fm; step fm; step fm
    show ⟨(a + 2) + 1, 0, 0, d + 1 + 1 + 1, (k + 1)⟩ [fm]⊢*
      ⟨a + 2 * (k + 1) + 3, 0, 0, d + 3 * (k + 1) + 3, 0⟩
    apply stepStar_trans (ih (a + 2) (d + 3))
    ring_nf; finish

-- Main transition
theorem main_trans (j m : ℕ) : ⟨j + m + 2, 0, 0, 3 * m + 1, 0⟩ [fm]⊢⁺
    ⟨j + 4 * m + 5, 0, 0, 9 * m + 7, 0⟩ := by
  -- d_to_c: ->* (j+m+2, 0, 3*m+1, 0, 0)
  have h1 : ⟨j + m + 2, 0, 0, 3 * m + 1, 0⟩ [fm]⊢*
      ⟨j + m + 2, 0, 3 * m + 1, 0, 0⟩ := by
    rw [show (3 * m + 1 : ℕ) = 0 + (3 * m + 1) from by ring]
    apply stepStar_trans (d_to_c (3 * m + 1) (j + m + 2) 0 0)
    ring_nf; finish
  -- R5 + R1: ->⁺ (j+m+1, 0, 3*m, 1, 2)
  have h2 : ⟨j + m + 2, 0, 3 * m + 1, 0, 0⟩ [fm]⊢⁺
      ⟨j + m + 1, 0, 3 * m, 1, 2⟩ := by
    rw [show j + m + 2 = (j + m + 1) + 1 from by ring,
        show 3 * m + 1 = (3 * m) + 1 from by ring]
    step fm; step fm; finish
  -- drain: ->* (j+1, 0, 0, 3*m+1, 2*m+2)
  have h3 : ⟨j + m + 1, 0, 3 * m, 1, 2⟩ [fm]⊢*
      ⟨j + 1, 0, 0, 3 * m + 1, 2 * m + 2⟩ := by
    rw [show j + m + 1 = (j + 1) + m from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (drain_chain m (j + 1) 1 1)
    ring_nf; finish
  -- climb: ->* (j+4*m+5, 0, 0, 9*m+7, 0)
  have h4 : ⟨j + 1, 0, 0, 3 * m + 1, 2 * m + 2⟩ [fm]⊢*
      ⟨j + 4 * m + 5, 0, 0, 9 * m + 7, 0⟩ := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
    apply stepStar_trans (climb (2 * m + 1) j (3 * m + 1))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 4, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨j, m⟩ ↦ ⟨j + m + 2, 0, 0, 3 * m + 1, 0⟩) ⟨0, 1⟩
  intro ⟨j, m⟩
  refine ⟨⟨j + m + 1, 3 * m + 2⟩, ?_⟩
  show ⟨j + m + 2, 0, 0, 3 * m + 1, 0⟩ [fm]⊢⁺ ⟨j + m + 1 + (3 * m + 2) + 2, 0, 0, 3 * (3 * m + 2) + 1, 0⟩
  rw [show j + m + 1 + (3 * m + 2) + 2 = j + 4 * m + 5 from by ring,
      show 3 * (3 * m + 2) + 1 = 9 * m + 7 from by ring]
  exact main_trans j m
