import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #551: [297/35, 4/5, 5/6, 7/11, 55/2]

Vector representation:
```
 0  3 -1 -1  1
 2  0 -1  0  0
-1 -1  1  0  0
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_551

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 repeated: convert e to d
theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  step fm
  apply stepStar_trans (ih _)
  ring_nf; finish

-- R1/R3 interleave: d rounds of (R1, R3) then final R1
theorem r1r3_interleave : ∀ d, ∀ a b e, ⟨a+d, b, 1, d+1, e⟩ [fm]⊢* ⟨a, b+2*d+3, 0, 0, e+d+1⟩ := by
  intro d; induction' d with d ih <;> intro a b e
  · step fm; ring_nf; finish
  rw [show a + (d + 1) = (a + d) + 1 from by omega]
  step fm; step fm
  apply stepStar_trans (ih a (b + 2) (e + 1))
  ring_nf; finish

-- R3/R2 drain: k rounds of (R3, R2) increasing a
theorem r3r2_drain : ∀ k, ∀ a e, ⟨a+1, k, 0, 0, e⟩ [fm]⊢* ⟨a+1+k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih (a + 1) e)
  ring_nf; finish

-- Main transition: (m+d+2, 0, 0, d+1, 0) →⁺ (m+2*d+4, 0, 0, d+2, 0)
theorem main_trans : ⟨m+d+2, 0, 0, d+1, 0⟩ [fm]⊢⁺ ⟨m+2*d+4, 0, 0, d+2, 0⟩ := by
  -- R5: one step, then compose ⊢* pieces
  rw [show m + d + 2 = (m + 1 + d) + 1 from by omega]
  step fm
  -- R1/R3 interleave: →*
  apply stepStar_trans (r1r3_interleave d (m + 1) 0 1)
  -- R3/R2 drain: →*
  rw [show 0 + 2 * d + 3 = 2 * d + 3 from by omega,
      show 1 + d + 1 = d + 2 from by omega]
  apply stepStar_trans (r3r2_drain (2 * d + 3) m (d + 2))
  -- e_to_d: →*
  rw [show m + 1 + (2 * d + 3) = m + 2 * d + 4 from by omega]
  have h := e_to_d (a := m + 2 * d + 4) (d + 2) 0
  simpa using h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, d⟩ ↦ ⟨m + d + 2, 0, 0, d + 1, 0⟩) ⟨0, 0⟩
  intro ⟨m, d⟩
  refine ⟨⟨m + d + 1, d + 1⟩, ?_⟩
  show ⟨m + d + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨(m + d + 1) + (d + 1) + 2, 0, 0, (d + 1) + 1, 0⟩
  rw [show (m + d + 1) + (d + 1) + 2 = m + 2 * d + 4 from by omega,
      show (d + 1) + 1 = d + 2 from by omega]
  exact main_trans

end Sz22_2003_unofficial_551
