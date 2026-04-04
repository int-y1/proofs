import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1732: [8/15, 33/14, 275/2, 7/11, 3/7]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1732

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r3_chain : ∀ a, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * a, 0, e + a⟩ := by
  intro a; induction' a with a ih generalizing c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 2) (e := e + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ⟨a + 1, 0, C + k + 1, k, E⟩ [fm]⊢* ⟨a + 1 + 2 * k, 0, C + 1, 0, E + k⟩ := by
  intro k; induction' k with k ih generalizing a C E
  · exists 0
  · rw [show C + (k + 1) + 1 = (C + k + 1) + 1 from by ring]
    step fm
    rw [show C + k + 1 + 1 = (C + 1) + k + 1 from by ring]
    step fm
    rw [show C + 1 + k = C + k + 1 from by ring]
    apply stepStar_trans (ih (a := a + 2) (C := C) (E := E + 1))
    ring_nf; finish

theorem main_trans (F E : ℕ) : ⟨0, 0, E + F + 2, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 0, (3 * E + 2) + (F + E + 3) + 2, 0, (3 * E + 2) + 1⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show (E + 1 : ℕ) = 0 + (E + 1) from by ring]
    exact e_to_d (E + 1) (c := E + F + 2) (d := 0) (e := 0)
  rw [show (0 : ℕ) + (E + 1) = E + 1 from by ring]
  step fm
  rw [show E + F + 2 = (E + F + 1) + 1 from by omega]
  step fm
  rw [show E + F + 1 = F + E + 1 from by ring]
  apply stepStar_trans (r2r1_chain E (a := 2) (C := F) (E := 0))
  rw [show (0 : ℕ) + E = E from by ring,
      show 2 + 1 + 2 * E = 3 + 2 * E from by ring]
  apply stepStar_trans (r3_chain (3 + 2 * E) (c := F + 1) (e := E))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, E⟩ ↦ ⟨0, 0, E + F + 2, 0, E + 1⟩) ⟨0, 0⟩
  intro ⟨F, E⟩
  exact ⟨⟨F + E + 3, 3 * E + 2⟩, main_trans F E⟩
