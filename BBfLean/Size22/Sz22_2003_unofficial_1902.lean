import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1902: [9/35, 65/33, 14/3, 11/13, 39/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  1  0  0
 0  0  0  0  1 -1
-1  1  0  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1902

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ a m j, ⟨a, m + 1, 0, j + k, k, m + 1⟩ [fm]⊢*
    ⟨a, m + k + 1, 0, j, 0, m + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a m j
  · exists 0
  · rw [show j + (k + 1) = j + k + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    rw [show j + k + 1 = (j + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (m + 1) j)
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a, k, 0, d, 0, f⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0, f⟩ := by
  intro k; induction' k with k ih generalizing a d f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a := a + 1) (d := d + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ⟨a, 0, 0, d, e, k⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (e := e + 1))
    ring_nf; finish

theorem r2r1_full : ⟨a, 1, 0, n + 1, n + 1, 1⟩ [fm]⊢*
    ⟨a, n + 2, 0, 0, 0, n + 2⟩ := by
  have h := r2r1_chain (n + 1) a 0 0
  simp only [Nat.zero_add] at h
  exact h

theorem main_trans : ⟨a + 1, 0, 0, n + 1, n + 1, 0⟩ [fm]⊢⁺
    ⟨a + n + 2, 0, 0, n + 2, n + 2, 0⟩ := by
  step fm
  apply stepStar_trans r2r1_full
  apply stepStar_trans (r3_chain (n + 2) (a := a) (d := 0) (f := n + 2))
  rw [show 0 + (n + 2) = n + 2 from by ring]
  apply stepStar_trans (r4_chain (n + 2) (a := a + (n + 2)) (d := n + 2) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a + 1, 0, 0, n + 1, n + 1, 0⟩) ⟨0, 0⟩
  intro ⟨a, n⟩; exact ⟨⟨a + n + 1, n + 1⟩, main_trans⟩
