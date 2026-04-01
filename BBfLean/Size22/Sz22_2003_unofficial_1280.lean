import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1280: [56/15, 21/22, 25/2, 11/7, 3/5]

Vector representation:
```
 3 -1 -1  1  0
-1  1  0  1 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1280

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R2+R1 chain: (3, 0, c+e, 1, e) ⊢* (3+2e, 0, c, 1+2e, 0)
theorem r2r1_chain : ∀ e, ∀ a c d,
    ⟨a + 1, 0, c + e, d, e⟩ [fm]⊢* ⟨a + 2 * e + 1, 0, c, d + 2 * e, 0⟩ := by
  intro e; induction' e with e ih
  · intro a c d; exists 0
  · intro a c d
    rw [show c + (e + 1) = (c + e) + 1 from by omega,
        show (e : ℕ) + 1 = e + 1 from rfl]
    step fm; step fm
    rw [show a + 3 = (a + 2) + 1 from by omega,
        show d + 1 + 1 = d + 2 from by omega]
    apply stepStar_trans (ih (a + 2) c (d + 2))
    ring_nf; finish

-- R3 drain: j steps of R3.
theorem r3_drain : ∀ j, ∀ c d,
    ⟨j, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * j, d, 0⟩ := by
  intro j; induction' j with j ih
  · intro c d; exists 0
  · intro c d
    step fm
    apply stepStar_trans (ih (c + 2) d)
    ring_nf; finish

-- R4 drain: transfer d to e.
theorem d_to_e : ∀ j, ∀ c d e,
    ⟨0, 0, c, d + j, e⟩ [fm]⊢* ⟨0, 0, c, d, e + j⟩ := by
  intro j; induction' j with j ih
  · intro c d e; exists 0
  · intro c d e
    rw [show d + (j + 1) = (d + j) + 1 from by omega]
    step fm
    apply stepStar_trans (ih c d (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, c+e+2, 0, e) ⊢⁺ (0, 0, c+4*e+6, 0, 2*e+1)
theorem main_trans (c e : ℕ) :
    ⟨0, 0, c + e + 2, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c + 4 * e + 6, 0, 2 * e + 1⟩ := by
  rw [show c + e + 2 = (c + e + 1) + 1 from by omega]
  step fm
  rw [show c + e + 1 = (c + e) + 1 from by omega]
  step fm
  -- State: (3, 0, c+e, 1, e). Apply r2r1_chain with a=2.
  rw [show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r2r1_chain e 2 c 1)
  -- State: (2+2*e+1, 0, c, 1+2*e, 0)
  rw [show 2 + 2 * e + 1 = 3 + 2 * e from by ring]
  apply stepStar_trans (r3_drain (3 + 2 * e) c (1 + 2 * e))
  rw [show c + 2 * (3 + 2 * e) = c + 4 * e + 6 from by ring,
      show 1 + 2 * e = 0 + (1 + 2 * e) from by ring]
  apply stepStar_trans (d_to_e (1 + 2 * e) (c + 4 * e + 6) 0 0)
  rw [show 0 + (1 + 2 * e) = 2 * e + 1 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, e⟩ ↦ ⟨0, 0, c + e + 2, 0, e⟩) ⟨0, 0⟩
  intro ⟨c, e⟩
  refine ⟨⟨c + 2 * e + 3, 2 * e + 1⟩, ?_⟩
  show ⟨0, 0, c + e + 2, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * e + 3 + (2 * e + 1) + 2, 0, 2 * e + 1⟩
  rw [show c + 2 * e + 3 + (2 * e + 1) + 2 = c + 4 * e + 6 from by ring]
  exact main_trans c e

end Sz22_2003_unofficial_1280
