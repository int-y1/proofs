import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1814: [9/10, 55/21, 2/3, 7/11, 825/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  1  2  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1814

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+2, d, e+1⟩
  | _ => none

theorem r1_chain : ∀ k, ⟨a + k, b, k, d, e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ⟨a + k, b + 1, 0, k, e⟩ [fm]⊢* ⟨a, b + k + 1, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    step fm
    rw [show (b + 1 + 1 : ℕ) = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b := b + 1) (e := e + 1))
    ring_nf; finish

theorem main_trans : ∀ n, ⟨2 * n + 5, 0, 0, n + 2, 0⟩ [fm]⊢⁺ ⟨2 * n + 7, 0, 0, n + 3, 0⟩ := by
  intro n
  step fm
  rw [show 2 * n + 4 = (2 * n + 2) + 2 from by ring]
  apply stepStar_trans (r1_chain 2 (a := 2 * n + 2) (b := 1) (d := n + 2) (e := 1))
  rw [show 1 + 2 * 2 = (5 : ℕ) from by ring,
      show 2 * n + 2 = n + (n + 2) from by ring,
      show (5 : ℕ) = 4 + 1 from by ring]
  apply stepStar_trans (r2r1_chain (n + 2) (a := n) (b := 4) (e := 1))
  rw [show 4 + (n + 2) + 1 = (n + 7 : ℕ) from by ring,
      show 1 + (n + 2) = (n + 3 : ℕ) from by ring]
  apply stepStar_trans (r3_chain (n + 7) (a := n) (e := n + 3))
  rw [show n + (n + 7) = 2 * n + 7 from by ring]
  apply stepStar_trans (r4_chain (n + 3) (a := 2 * n + 7))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 2, 0⟩) (by execute fm 22)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 5, 0, 0, n + 2, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
