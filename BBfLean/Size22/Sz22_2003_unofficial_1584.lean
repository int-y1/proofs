import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1584: [7/45, 605/21, 2/3, 3/11, 63/2]

Vector representation:
```
 0 -2 -1  1  0
 0 -1  1 -1  2
 1 -1  0  0  0
 0  1  0  0 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1584

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R4,R2 chain: each round does R4 (e to b) then R2 (b+d to c+e).
theorem r4r2_chain : ∀ k, ∀ a c e,
    ⟨a, 0, c, k, e + 1⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · step fm; step fm
    rw [show e + 2 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih a (c + 1) (e + 1)); ring_nf; finish

-- R4,R3 chain: drains e, builds a.
theorem r4r3_chain : ∀ k, ∀ a c,
    ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a + k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [Nat.add_succ]; step fm; step fm
    apply stepStar_trans (ih (a + 1) c); ring_nf; finish

-- R5,R1 chain: drains a and c, builds d.
theorem r5r1_chain : ∀ k, ∀ a d,
    ⟨a + k, 0, k, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm; step fm
    apply stepStar_trans (ih a (d + 2)); ring_nf; finish

-- Main transition: (a+1, 0, 0, d+2, 0) ⊢⁺ (a+2, 0, 0, 2*d+6, 0)
theorem main_trans (a d : ℕ) :
    ⟨a + 1, 0, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 2 * d + 6, 0⟩ := by
  -- R5: -> (a, 2, 0, d+3, 0)
  step fm
  rw [show d + 2 + 1 = (d + 2) + 1 from by ring]
  -- R2: -> (a, 1, 1, d+1+1, 2)
  step fm
  -- R2: -> (a, 0, 2, d+1, 4)
  rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
  step fm
  -- r4r2_chain k=(d+1), c=2, e=3: (a, 0, 2, d+1, 3+1) -> (a, 0, d+3, 0, d+5)
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r4r2_chain (d + 1) a 2 3)
  rw [show 2 + (d + 1) = d + 3 from by ring,
      show 3 + (d + 1) + 1 = d + 5 from by ring]
  -- r4r3_chain k=(d+5): (a, 0, d+3, 0, d+5) -> (a+d+5, 0, d+3, 0, 0)
  apply stepStar_trans (r4r3_chain (d + 5) a (d + 3))
  -- r5r1_chain k=(d+3), a_param=(a+2): ((a+2)+(d+3), 0, d+3, 0, 0) -> (a+2, 0, 0, 2*(d+3), 0)
  rw [show a + (d + 5) = (a + 2) + (d + 3) from by ring,
      show (0 : ℕ) = 0 + 2 * 0 from by ring]
  apply stepStar_trans (r5r1_chain (d + 3) (a + 2) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 1, 0, 0, d + 2, 0⟩) ⟨1, 0⟩
  intro ⟨a, d⟩; exact ⟨⟨a + 1, 2 * d + 4⟩, main_trans a d⟩

end Sz22_2003_unofficial_1584
