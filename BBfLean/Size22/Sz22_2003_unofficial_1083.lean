import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1083: [5/6, 196/55, 847/2, 3/7, 5/3]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1  2 -1
-1  0  0  1  2
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude
-/

namespace Sz22_2003_unofficial_1083

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

private theorem r4_chain : ∀ k, ∀ b e,
    ⟨(0 : ℕ), b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) e

private theorem r5_chain : ∀ k, ∀ e,
    ⟨(0 : ℕ), k, 0, 0, e⟩ [fm]⊢* ⟨0, 0, k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro e
  · finish
  · step fm; exact ih e

private theorem r2_chain : ∀ k, ∀ a d e,
    ⟨a, (0 : ℕ), k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm; exact ih (a + 2) (d + 2) e

private theorem r3_chain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; exact ih (d + 1) (e + 2)

private theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, n + 1, n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * n + 4, 4 * n + 5⟩ := by
  -- First R4 step to establish ⊢⁺
  rw [show n + 1 = n + 0 + 1 from by ring]
  step fm
  -- Remaining R4 steps: (0, 1, 0, n, n+2) → (0, n+1, 0, 0, n+2)
  apply stepPlus_stepStar_stepPlus
  · have := r4_chain n 1 (n + 2)
    convert this using 1; ring_nf
  -- R5 chain: (0, n+1, 0, 0, n+2) → (0, 0, n+1, 0, n+2)
  apply stepStar_trans
  · exact r5_chain (n + 1) (n + 2)
  -- R2 chain: (0, 0, n+1, 0, n+2) → (2n+2, 0, 0, 2n+2, 1)
  apply stepStar_trans
  · have := r2_chain (n + 1) 0 0 1
    convert this using 1 <;> ring
  -- R3 chain: (2n+2, 0, 0, 2n+2, 1) → (0, 0, 0, 4n+4, 4n+5)
  have := r3_chain (2 * n + 2) (2 * n + 2) 1
  convert this using 1 <;> ring

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 1, n + 2⟩) 0
  intro n; exists 4 * n + 3
  have := main_trans n
  convert this using 2 <;> ring

end Sz22_2003_unofficial_1083
