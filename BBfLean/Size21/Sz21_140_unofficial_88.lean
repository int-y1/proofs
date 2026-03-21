import BBfLean.FM

/-!
# sz21_140_unofficial #88: [5/6, 539/2, 44/35, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  1
 0  1  0  0 -1
 0  0  1 -1  0
```

TODO: After finishing the proof, replace this paragraph with one of:
* This Fractran program doesn't halt.
* This Fractran program halts.

Author: (replace this with the author of the proof)
-/

namespace Sz21_140_unofficial_88

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem nonhalt : ¬halts fm c₀ := by
  sorry
