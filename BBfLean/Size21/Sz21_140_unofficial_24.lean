import BBfLean.FM

/-!
# sz21_140_unofficial #24: [28/15, 3/22, 65/2, 11/7, 21/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 0  1  0  1  0 -1
```

TODO: After finishing the proof, replace this paragraph with one of:
* This Fractran program doesn't halt.
* This Fractran program halts.

Author: (replace this with the author of the proof)
-/

namespace Sz21_140_unofficial_24

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

theorem nonhalt : ¬halts fm c₀ := by
  sorry
