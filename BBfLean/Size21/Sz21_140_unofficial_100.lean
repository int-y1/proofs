import BBfLean.FM

/-!
# sz21_140_unofficial #100: [7/15, 22/3, 27/77, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  1
 0  3  0 -1 -1
 0  0  1  0 -1
-1  1  0  0  1
```

TODO: After finishing the proof, replace this paragraph with one of:
* This Fractran program doesn't halt.
* This Fractran program halts.
-/

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem nonhalt : ¬halts fm c₀ := by
  sorry
