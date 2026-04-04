import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1822: [9/10, 55/21, 4/3, 7/11, 99/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  0
 0  0  0  1 -1
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1822

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ a b e,
    ⟨a + k, b + 1, 0, k, e⟩ [fm]⊢* ⟨a, b + 1 + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a e,
    ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 2) e)
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ a d,
    ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

theorem main_trans : ∀ F d,
    ⟨F + d + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨F + 2 * d + 6, 0, 0, d + 2, 0⟩ := by
  intro F d
  -- R5: (F+d+2, 0, 0, d+1, 0) → (F+d+1, 2, 0, d+1, 1)
  -- Note: F+d+2 = (F+d+1)+1, so after R5 we get (F+d+1, 2, 0, d+1, 1)
  -- F+d+1 = F + (d+1), so chain applies with a=F, k=d+1
  step fm
  apply stepStar_trans (r2r1_chain (d + 1) F 1 1)
  rw [show 1 + 1 + (d + 1) = d + 3 from by ring,
      show 1 + (d + 1) = d + 2 from by ring]
  apply stepStar_trans (r3_chain (d + 3) F (d + 2))
  apply stepStar_trans (r4_chain (d + 2) (F + 2 * (d + 3)) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, d⟩ ↦ ⟨F + d + 2, 0, 0, d + 1, 0⟩) ⟨2, 0⟩
  intro ⟨F, d⟩
  refine ⟨⟨F + d + 3, d + 1⟩, ?_⟩
  show ⟨F + d + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨F + d + 3 + (d + 1) + 2, 0, 0, (d + 1) + 1, 0⟩
  rw [show F + d + 3 + (d + 1) + 2 = F + 2 * d + 6 from by ring,
      show (d + 1) + 1 = d + 2 from by ring]
  exact main_trans F d
