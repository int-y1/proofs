import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1734: [8/15, 33/14, 5/2, 7/11, 44/5]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 2  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1734

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k c d, ⟨(0 : ℕ), 0, c, d, k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

theorem a_to_c : ∀ k c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c e, ⟨a + 2, 0, c + k, k, e⟩ [fm]⊢* ⟨a + 2 * k + 2, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    step fm
    rw [show a + 2 + 2 = (a + 2) + 2 from by ring]
    apply stepStar_trans (ih (a + 2) c (e + 1))
    ring_nf; finish

theorem main_trans : ∀ f e, ⟨(0 : ℕ), 0, e + f + 1, 0, e⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, (e + 1) + (f + e) + 1, 0, e + 1⟩ := by
  intro f e
  apply stepStar_stepPlus_stepPlus (e_to_d e (e + f + 1) 0)
  rw [show (0 : ℕ) + e = e from Nat.zero_add e]
  rw [show e + f + 1 = (e + f) + 1 from rfl]
  step fm
  rw [show (e : ℕ) + f = f + e from by ring]
  show ⟨(0 : ℕ) + 2, 0, f + e, e, 1⟩ [fm]⊢* ⟨(0 : ℕ), 0, (e + 1) + (f + e) + 1, 0, e + 1⟩
  apply stepStar_trans (r2r1_chain e 0 f 1)
  rw [show 0 + 2 * e + 2 = 2 * e + 2 from by ring,
      show 1 + e = e + 1 from by ring]
  apply stepStar_trans (a_to_c (2 * e + 2) f (e + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨f, e⟩ ↦ ⟨0, 0, e + f + 1, 0, e⟩) ⟨0, 1⟩
  intro ⟨f, e⟩; exact ⟨⟨f + e, e + 1⟩, main_trans f e⟩
