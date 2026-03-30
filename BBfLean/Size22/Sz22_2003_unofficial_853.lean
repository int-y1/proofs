import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #853: [36/35, 5/3, 1/10, 2401/2, 5/7]

Vector representation:
```
 2  2 -1 -1
 0 -1  1  0
-1  0 -1  0
-1  0  0  4
 0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_853

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+2, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a+1, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+4⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | _ => none

-- R4 drain: (a+k, 0, 0, d) →* (a, 0, 0, d + 4*k)
theorem r4_drain : ∀ k, ∀ a d, ⟨a + k, 0, 0, d⟩ [fm]⊢* ⟨a, 0, 0, d + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 4))
    ring_nf; finish

-- R1-R2 interleave: (A, B, 1, k+1) →* (A + 2*(k+1), B + k + 2, 0, 0)
theorem r1r2_interleave : ∀ k, ∀ A B, ⟨A, B, 1, k + 1⟩ [fm]⊢* ⟨A + 2 * (k + 1), B + k + 2, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B
  · step fm; ring_nf; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (A + 2) (B + 1))
    ring_nf; finish

-- R2 drain: (A, B+k, C, 0) →* (A, B, C+k, 0)
theorem b_to_c : ∀ k, ∀ A B C, ⟨A, B + k, C, 0⟩ [fm]⊢* ⟨A, B, C + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B C
  · exists 0
  · rw [show B + (k + 1) = (B + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih A B (C + 1))
    ring_nf; finish

-- R3 drain: (A + k, 0, C + k, 0) →* (A, 0, C, 0)
theorem r3_drain : ∀ k, ∀ A C, ⟨A + k, 0, C + k, 0⟩ [fm]⊢* ⟨A, 0, C, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + (k + 1) = (C + k) + 1 from by ring]
    step fm
    exact ih A C

-- Full cycle as ⊢*: (a+2, 0, 0, 0) →* (4a+6, 0, 0, 0)
theorem cycle_star (a : ℕ) : ⟨a + 2, 0, 0, 0⟩ [fm]⊢* ⟨4 * a + 6, 0, 0, 0⟩ := by
  -- R4 drain
  rw [show a + 2 = 0 + (a + 2) from by ring]
  apply stepStar_trans (r4_drain (a + 2) 0 0)
  -- R5
  rw [show 0 + 4 * (a + 2) = (4 * a + 6 + 1) + 1 from by ring]
  step fm
  -- Interleave
  apply stepStar_trans (r1r2_interleave (4 * a + 6) 0 0)
  -- b_to_c
  rw [show 0 + (4 * a + 6) + 2 = 0 + (4 * a + 8) from by ring]
  apply stepStar_trans (b_to_c (4 * a + 8) (0 + 2 * (4 * a + 6 + 1)) 0 0)
  -- r3_drain
  rw [show 0 + 2 * (4 * a + 6 + 1) = (4 * a + 6) + (4 * a + 8) from by ring,
      show 0 + (4 * a + 8) = 0 + (4 * a + 8) from by ring]
  exact r3_drain (4 * a + 8) (4 * a + 6) 0

-- Main transition as ⊢⁺
theorem main_trans (a : ℕ) : ⟨a + 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨4 * a + 6, 0, 0, 0⟩ := by
  apply stepStar_stepPlus (cycle_star a)
  intro h; have := congr_arg Prod.fst h; simp at this; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0⟩)
  · execute fm 15
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0⟩) 0
  intro n; exact ⟨4 * n + 4, main_trans n⟩

end Sz22_2003_unofficial_853
