import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #85: [1/30, 1323/2, 2/77, 5/7, 22/3]

Vector representation:
```
-1 -1 -1  0  0
-1  3  0  2  0
 1  0  0 -1 -1
 0  0  1 -1  0
 1 -1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_85

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

theorem transition (n : ℕ) : (⟨0, n+1, 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨0, n+3, 0, 0, 0⟩ := by
  execute fm 10

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 3, 0, 0, 0⟩) (by execute fm 15)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2*n+3, 0, 0, 0⟩) 0
  intro n; exists n+1
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
  rw [show 2 * (n + 1) + 3 = (2 * n + 2) + 3 from by ring]
  exact transition (2 * n + 2)
