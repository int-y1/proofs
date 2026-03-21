import BBfLean.FM

/-!
# sz21_140_unofficial #107: [7/30, 44/21, 9/2, 5/11, 7/3]

Vector representation:
```
-1 -1 -1  1  0
 2 -1  0 -1  1
-1  2  0  0  0
 0  0  1  0 -1
 0 -1  0  1  0
```

TODO: After finishing the proof, replace this paragraph with one of:
* This Fractran program doesn't halt.
* This Fractran program halts.

Author: (replace this with the author of the proof)
-/

namespace Sz21_140_unofficial_107

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

theorem nonhalt : ¬halts fm c₀ := by
  sorry
