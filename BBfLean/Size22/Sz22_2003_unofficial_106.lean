import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #106: [1/30, 49/3, 12/77, 10/7, 33/2]

Vector representation:
```
-1 -1 -1  0  0
 0 -1  0  2  0
 2  1  0 -1 -1
 1  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_106

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R3+R2 interleave: each pair consumes 1 from e, adds 2 to a, adds 1 to d
theorem r3r2_chain : ∀ k, ∀ a d,
    (⟨a, 0, 0, d + 1, k + 1⟩ : Q) [fm]⊢* ⟨a + 2 * k + 2, 0, 0, d + k + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; ring_nf; finish
  step fm; step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]
  apply stepStar_trans (ih (a + 2) (d + 1))
  ring_nf; finish

-- R4 chain: each step adds 1 to a and c, removes 1 from d
theorem r4_chain : ∀ d, ∀ a c,
    (⟨a, 0, c, d, 0⟩ : Q) [fm]⊢* ⟨a + d, 0, c + d, 0, 0⟩ := by
  intro d; induction' d with d ih <;> intro a c
  · exists 0
  step fm
  apply stepStar_trans (ih (a + 1) (c + 1))
  ring_nf; finish

-- R5+R1 alternating: each pair removes 2 from a, 1 from c, adds 1 to e
theorem r5r1_chain : ∀ k, ∀ a e,
    (⟨a + 2 * k, 0, k, 0, e⟩ : Q) [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show a + 2 * (k + 1) = (a + 2 * k) + 1 + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih a (e + 1))
  ring_nf; finish

-- Main transition: (a+1, 0, 0, 0, e+3) →⁺ (a+e+2, 0, 0, 0, e+6)
theorem main_trans : ∀ a e,
    (⟨a + 1, 0, 0, 0, e + 3⟩ : Q) [fm]⊢⁺ ⟨a + e + 2, 0, 0, 0, e + 6⟩ := by
  intro a e
  -- Phase 1 (R5, R2): (a+1, 0, 0, 0, e+3) → (a, 1, 0, 0, e+4) → (a, 0, 0, 2, e+4)
  step fm; step fm
  -- Phase 2 (R3+R2 chain): (a, 0, 0, 2, e+4)
  -- Write 2 = 1+1, e+4 = (e+3)+1, apply r3r2_chain with k=e+3, d=1
  -- Result: (a+2*(e+3)+2, 0, 0, 1+(e+3)+2, 0) = (a+2e+8, 0, 0, e+6, 0)
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  rw [show e + 4 = (e + 3) + 1 from by ring]
  apply stepStar_trans (r3r2_chain (e + 3) a 1)
  -- Phase 3 (R4 chain): (a+2*(e+3)+2, 0, 0, 1+(e+3)+2, 0)
  -- = (a+2e+8, 0, 0, e+6, 0)
  -- Apply r4_chain with d=e+6, a'=a+2e+8, c=0
  -- Result: (a+2e+8+(e+6), 0, e+6, 0, 0) = (a+3e+14, 0, e+6, 0, 0)
  rw [show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (r4_chain (1 + (e + 3) + 2) (a + 2 * (e + 3) + 2) 0)
  -- Phase 4 (R5+R1 chain): normalize then apply r5r1_chain
  rw [show a + 2 * (e + 3) + 2 + (1 + (e + 3) + 2) = (a + e + 2) + 2 * (1 + (e + 3) + 2) from by ring]
  rw [show (0 : ℕ) + (1 + (e + 3) + 2) = 1 + (e + 3) + 2 from by ring]
  apply stepStar_trans (r5r1_chain (1 + (e + 3) + 2) (a + e + 2) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩)
  · execute fm 28
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e + 3⟩)
  · intro q ⟨a, e, hq⟩; subst hq
    exact ⟨⟨a + e + 2, 0, 0, 0, e + 6⟩,
           ⟨a + e + 1, e + 3, by ring_nf⟩,
           main_trans a e⟩
  · exact ⟨1, 0, by ring_nf⟩

end Sz22_2003_unofficial_106
