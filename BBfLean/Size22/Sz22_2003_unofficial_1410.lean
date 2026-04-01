import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1410: [7/15, 11/3, 54/77, 125/2, 3/5]

Vector representation:
```
 0 -1 -1  1  0
 0 -1  0  0  1
 1  3  0 -1 -1
-1  0  3  0  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1410

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+3, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: convert a to c
theorem r4_chain : ∀ k, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 3))
    ring_nf; finish

-- Drain: R3 + R2x3 repeated
theorem drain : ∀ k, ⟨a, 0, 0, k, e + 1⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + 1 + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm
    step fm
    step fm
    step fm
    rw [show e + 3 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (e := e + 2))
    ring_nf; finish

-- Interleave: R3 + R1x3 repeated
theorem interleave : ∀ k, ⟨a, 0, 3 * k + c, d + 1, e + k⟩ [fm]⊢*
    ⟨a + k, 0, c, d + 1 + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing a c d e
  · ring_nf; finish
  · rw [show 3 * (k + 1) + c = (3 * k + c) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    step fm
    step fm
    rw [show d + 3 = (d + 2) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (c := c) (d := d + 2) (e := e))
    ring_nf; finish

-- Middle phase: R5, R1, interleave, then R3+R1+R2x2
theorem middle_phase : ⟨0, 0, 3 * A + 3, 0, E + A + 1⟩ [fm]⊢*
    ⟨A + 1, 0, 0, 2 * A + 1, E + 2⟩ := by
  step fm
  step fm
  rw [show E + A + 1 = (E + 1) + A from by ring]
  apply stepStar_trans (interleave A (a := 0) (c := 1) (d := 0) (e := E + 1))
  rw [show 0 + A = A from by ring, show 0 + 1 + 2 * A = 2 * A + 1 from by ring]
  step fm
  step fm
  step fm
  step fm
  ring_nf; finish

-- Full transition
theorem full_transition : ⟨A + 2, 0, 0, 0, E + A + 2⟩ [fm]⊢⁺
    ⟨3 * A + 5, 0, 0, 0, E + 4 * A + 8⟩ := by
  rw [show A + 2 = (A + 1) + 1 from by ring]
  step fm
  rw [show A + 1 = 0 + (A + 1) from by ring]
  apply stepStar_trans (r4_chain (A + 1) (a := 0) (c := 3) (e := E + A + 2))
  rw [show 3 + 3 * (A + 1) = 3 * (A + 1) + 3 from by ring,
      show E + A + 2 = E + (A + 1) + 1 from by ring]
  apply stepStar_trans (middle_phase (A := A + 1) (E := E))
  rw [show A + 1 + 1 = A + 2 from by ring, show 2 * (A + 1) + 1 = 2 * A + 3 from by ring]
  rw [show E + 2 = (E + 1) + 1 from by ring]
  apply stepStar_trans (drain (2 * A + 3) (a := A + 2) (e := E + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 6⟩) (by execute fm 20)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + 2, 0, 0, 0, e + a + 2⟩) ⟨0, 4⟩
  intro ⟨a, e⟩
  refine ⟨⟨3 * a + 3, e + a + 3⟩, ?_⟩
  show (a + 2, 0, 0, 0, e + a + 2) [fm]⊢⁺ (3 * a + 3 + 2, 0, 0, 0, (e + a + 3) + (3 * a + 3) + 2)
  rw [show 3 * a + 3 + 2 = 3 * a + 5 from by ring,
      show (e + a + 3) + (3 * a + 3) + 2 = e + 4 * a + 8 from by ring]
  exact full_transition

end Sz22_2003_unofficial_1410
