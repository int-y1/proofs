import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #862: [4/105, 1/22, 15/2, 11/3, 98/55]

Vector representation:
```
 2 -1 -1 -1  0
-1  0  0  0 -1
-1  1  1  0  0
 0 -1  0  0  1
 1  0 -1  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_862

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

-- R3 chain: (k, b, c, 0, 0) →* (0, b+k, c+k, 0, 0)
theorem r3_chain : ∀ k, ∀ b c, ⟨k, b, c, 0, 0⟩ [fm]⊢* ⟨0, b + k, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) (c + 1))
    ring_nf; finish

-- R4 chain: (0, k, c, 0, e) →* (0, 0, c, 0, e+k)
theorem r4_chain : ∀ k, ∀ c e, ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih c (e + 1))
    ring_nf; finish

-- R5+R2 drain: (0, 0, c+k+1, d, 2*k+1) →* (1, 0, c, d+2*k+2, 0)
theorem r5r2_drain : ∀ k, ∀ c d, ⟨0, 0, c + k + 1, d, 2 * k + 1⟩ [fm]⊢* ⟨1, 0, c, d + 2 * k + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · step fm; finish
  · rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih c (d + 2))
    ring_nf; finish

-- R3+R1 chain: (a+1, 0, c, k, 0) →* (a+1+k, 0, c, 0, 0)
theorem r3r1_chain : ∀ k, ∀ a c, ⟨a + 1, 0, c, k, 0⟩ [fm]⊢* ⟨a + 1 + k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (a + 1) c)
    ring_nf; finish

-- Main transition: (2*m+3, 0, c, 0, 0) →⁺ (2*m+5, 0, c+m+1, 0, 0)
theorem main_trans (m c : ℕ) :
    ⟨2 * m + 3, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨2 * m + 5, 0, c + m + 1, 0, 0⟩ := by
  -- First step via R3
  step fm
  -- Now at (2*m+2, 1, c+1, 0, 0). Continue with R3 chain for remaining 2*m+2 steps.
  apply stepStar_trans (r3_chain (2 * m + 2) 1 (c + 1))
  -- Now at (0, 2*m+3, c+2*m+3, 0, 0). R4 chain.
  show ⟨0, 1 + (2 * m + 2), c + 1 + (2 * m + 2), 0, 0⟩ [fm]⊢* ⟨2 * m + 5, 0, c + m + 1, 0, 0⟩
  rw [show 1 + (2 * m + 2) = 2 * m + 3 from by ring,
      show c + 1 + (2 * m + 2) = c + (2 * m + 3) from by ring]
  apply stepStar_trans (r4_chain (2 * m + 3) (c + (2 * m + 3)) 0)
  -- Now at (0, 0, c+2m+3, 0, 2m+3). R5+R2 drain.
  show ⟨0, 0, c + (2 * m + 3), 0, 0 + (2 * m + 3)⟩ [fm]⊢* ⟨2 * m + 5, 0, c + m + 1, 0, 0⟩
  rw [show 0 + (2 * m + 3) = 2 * (m + 1) + 1 from by ring,
      show c + (2 * m + 3) = (c + m + 1) + (m + 1) + 1 from by ring]
  apply stepStar_trans (r5r2_drain (m + 1) (c + m + 1) 0)
  -- Now at (1, 0, c+m+1, 2m+4, 0). R3+R1 chain.
  show ⟨1, 0, c + m + 1, 0 + 2 * (m + 1) + 2, 0⟩ [fm]⊢* ⟨2 * m + 5, 0, c + m + 1, 0, 0⟩
  rw [show 0 + 2 * (m + 1) + 2 = 2 * m + 4 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1_chain (2 * m + 4) 0 (c + m + 1))
  show ⟨0 + 1 + (2 * m + 4), 0, c + m + 1, 0, 0⟩ [fm]⊢* ⟨2 * m + 5, 0, c + m + 1, 0, 0⟩
  rw [show 0 + 1 + (2 * m + 4) = 2 * m + 5 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 0⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, c⟩ ↦ ⟨2 * m + 3, 0, c, 0, 0⟩) ⟨0, 0⟩
  intro ⟨m, c⟩; exact ⟨⟨m + 1, c + m + 1⟩, main_trans m c⟩
