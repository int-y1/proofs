import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1826: [9/10, 55/21, 44/3, 7/11, 9/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  1
 0  0  0  1 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1826

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

theorem interleave : ∀ k, ∀ b, ⟨a + k, b + 1, 0, k, e⟩ [fm]⊢* ⟨a, b + k + 1, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · intro b; exists 0
  · intro b
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    step fm
    apply stepStar_trans (ih (a := a) (e := e + 1) (b + 1))
    ring_nf; finish

theorem main_trans : ⟨F + d + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨F + 2 * d + 4, 0, 0, 2 * d + 2, 0⟩ := by
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (interleave d (a := F) (e := 0) 1)
  rw [show 1 + d + 1 = d + 2 from by ring,
      show 0 + d = d from by ring]
  apply stepStar_trans (r3_chain (d + 2) (a := F) (e := d))
  show ⟨F + 2 * (d + 2), 0, 0, 0, d + (d + 2)⟩ [fm]⊢* ⟨F + 2 * d + 4, 0, 0, 2 * d + 2, 0⟩
  rw [show F + 2 * (d + 2) = F + 2 * d + 4 from by ring,
      show d + (d + 2) = 0 + (2 * d + 2) from by ring]
  apply stepStar_trans (e_to_d (2 * d + 2) (a := F + 2 * d + 4) (d := 0) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 2, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, d⟩ ↦ ⟨F + d + 1, 0, 0, d, 0⟩) ⟨1, 2⟩
  intro ⟨F, d⟩
  refine ⟨⟨F + 1, 2 * d + 2⟩, ?_⟩
  show ⟨F + d + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨F + 1 + (2 * d + 2) + 1, 0, 0, 2 * d + 2, 0⟩
  rw [show F + 1 + (2 * d + 2) + 1 = F + 2 * d + 4 from by ring]
  exact main_trans

end Sz22_2003_unofficial_1826
