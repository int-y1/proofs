import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1958: [945/2, 2/55, 1/5, 121/63, 5/3]

Vector representation:
```
-1  3  1  1  0
 1  0 -1  0 -1
 0  0 -1  0  0
 0 -2  0 -1  2
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1958

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+2, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem spiral : ∀ n, ⟨(0 : ℕ), b, 1, k, n⟩ [fm]⊢* ⟨(0 : ℕ), b + 3 * n, 1, k + n, 0⟩ := by
  intro n; induction' n with n ih generalizing b k
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (b := b + 3) (k := k + 1))
    ring_nf; finish

theorem r4_drain : ∀ n b e, ⟨(0 : ℕ), b + 2 * n, 0, n, e⟩ [fm]⊢* ⟨(0 : ℕ), b, 0, 0, e + 2 * n⟩ := by
  intro n; induction' n with n ih
  · intro b e; exists 0
  · intro b e
    rw [show b + 2 * (n + 1) = b + 2 * n + 2 from by ring,
        show (n : ℕ) + 1 = (n + 1) from rfl]
    step fm
    rw [show b + 2 * n = b + 2 * n from rfl]
    apply stepStar_trans (ih b (e + 2))
    ring_nf; finish

theorem main_trans : ⟨(0 : ℕ), b + 1, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), b + e + 1, 0, 0, 2 * e + 2⟩ := by
  step fm
  apply stepStar_trans (spiral (e + 1) (b := b) (k := 0))
  step fm
  rw [show b + 3 * (e + 1) = (b + e + 1) + 2 * (e + 1) from by ring,
      show 0 + (e + 1) = e + 1 from by ring]
  apply stepStar_trans (r4_drain (e + 1) (b + e + 1) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 2⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨b, e⟩ ↦ ⟨0, b + 1, 0, 0, e + 1⟩) ⟨0, 1⟩
  intro ⟨b, e⟩
  refine ⟨⟨b + e, 2 * e + 1⟩, ?_⟩
  show ⟨(0 : ℕ), b + 1, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), (b + e) + 1, 0, 0, (2 * e + 1) + 1⟩
  rw [show (2 * e + 1) + 1 = 2 * e + 2 from by ring]
  exact main_trans
