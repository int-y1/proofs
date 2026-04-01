import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1560: [7/45, 20/21, 11/3, 3/2, 63/11]

Vector representation:
```
 0 -2 -1  1  0
 2 -1  1 -1  0
 0 -1  0  0  1
-1  1  0  0  0
 0  2  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1560

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- Phase: R2/R4 chain drains d.
-- From (a+2, 1, c+1, k+1, e) does R2,R4 then recurse.
theorem r2r4_chain : ∀ k, ∀ a c e, ⟨a + 2, 1, c + 1, k, e⟩ [fm]⊢* ⟨a + k + 2, 1, c + k + 1, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · step fm; step fm
    rw [show a + 3 = (a + 1) + 2 from by ring,
        show c + 1 + 1 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (c + 1) e); ring_nf; finish

-- Phase: R4/R3 drain a with d=0.
-- From (a, 0, c, 0, e) drains a via R4,R3 to reach (0, 0, c, 0, e+a).
theorem r4r3_drain : ∀ j, ∀ c e, ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + j⟩ := by
  intro j; induction' j with j ih <;> intro c e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih c (e + 1)); ring_nf; finish

-- Phase: R5/R1 chain drains c and e simultaneously.
-- From (0, 0, c, d, e+c) does c rounds of R5,R1 to reach (0, 0, 0, d+2*c, e).
theorem r5r1_chain : ∀ k, ∀ d e, ⟨0, 0, k, d, e + k⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (d + 2) e); ring_nf; finish

-- Main transition: (0, 0, 0, d, e+1) ⊢⁺ (0, 0, 0, 2*d+2, e+2)
theorem main_trans (d e : ℕ) :
    ⟨0, 0, 0, d, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 2, e + 2⟩ := by
  -- R5: (0,0,0,d,e+1) -> (0,2,0,d+1,e)
  step fm
  -- R2: (0,2,0,d+1,e) -> (2,1,1,d,e)
  step fm
  -- Now at (2,1,1,d,e). Apply R2/R4 chain to drain d.
  rw [show (2 : ℕ) = 0 + 2 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r2r4_chain d 0 0 e)
  rw [show 0 + d + 2 = d + 2 from by ring,
      show 0 + d + 1 = d + 1 from by ring]
  -- Now at (d+2, 1, d+1, 0, e). R3 fires (b=1, d=0).
  step fm
  -- Now at (d+2, 0, d+1, 0, e+1). R4/R3 drain.
  apply stepStar_trans (r4r3_drain (d + 2) (d + 1) (e + 1))
  rw [show e + 1 + (d + 2) = (e + 2) + (d + 1) from by ring]
  apply stepStar_trans (r5r1_chain (d + 1) 0 (e + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d, e + 1⟩) ⟨0, 0⟩
  intro ⟨d, e⟩; exact ⟨⟨2 * d + 2, e + 1⟩, main_trans d e⟩

end Sz22_2003_unofficial_1560
