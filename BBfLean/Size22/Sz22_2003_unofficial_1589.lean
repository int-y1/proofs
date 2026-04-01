import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1589: [70/3, 6/55, 1/5, 121/2, 1/77, 5/11]

Vector representation:
```
 1 -1  1  1  0
 1  1 -1  0 -1
 0  0 -1  0  0
-1  0  0  0  2
 0  0  0 -1 -1
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1589

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R1R2 chain: (a+1, 1, 0, d, E) ⊢* (a+2E+2, 0, 0, d+E+1, 0)
theorem r1r2_chain : ∀ E, ∀ a d,
    ⟨a + 1, 1, 0, d, E⟩ [fm]⊢* ⟨a + 2 * E + 2, 0, 0, d + E + 1, 0⟩ := by
  intro E; induction' E with E ih <;> intro a d
  · step fm; step fm; ring_nf; finish
  · step fm; step fm
    apply stepStar_trans (ih (a + 2) (d + 1)); ring_nf; finish

-- R4 drain: (a, 0, 0, d, e) ⊢* (0, 0, 0, d, e + 2*a)
theorem r4_drain : ∀ a, ∀ d e,
    ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * a⟩ := by
  intro a; induction' a with a ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 2)); ring_nf; finish

-- R5 drain: (0, 0, 0, d, e + d) ⊢* (0, 0, 0, 0, e)
theorem r5_drain : ∀ d e,
    ⟨0, 0, 0, d, e + d⟩ [fm]⊢* ⟨0, 0, 0, 0, e⟩ := by
  intro d; induction' d with d ih <;> intro e
  · exists 0
  · rw [show e + (d + 1) = e + d + 1 from by ring]
    step fm
    exact ih e

-- Main transition: (0, 0, 0, 0, n + 2) ⊢⁺ (0, 0, 0, 0, 3*n + 3)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 0, n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 0, 3 * n + 3⟩ := by
  -- R6: (0,0,0,0,n+2) -> (0,0,1,0,n+1)
  rw [show n + 2 = n + 1 + 1 from by ring]
  step fm
  -- R2: (0,0,1,0,n+1) -> (1,1,0,0,n)
  step fm
  -- R1R2 chain: (1,1,0,0,n) -> (2n+2,0,0,n+1,0)
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (r1r2_chain n 0 0)
  rw [show 0 + 2 * n + 2 = 2 * n + 2 from by ring,
      show 0 + n + 1 = n + 1 from by ring]
  -- R4 drain: (2n+2,0,0,n+1,0) -> (0,0,0,n+1,4n+4)
  apply stepStar_trans (r4_drain (2 * n + 2) (n + 1) 0)
  rw [show 0 + 2 * (2 * n + 2) = 4 * n + 4 from by ring]
  -- R5 drain: (0,0,0,n+1,4n+4) -> (0,0,0,0,3n+3)
  rw [show 4 * n + 4 = (3 * n + 3) + (n + 1) from by ring]
  exact r5_drain (n + 1) (3 * n + 3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 0, n + 2⟩) 0
  intro n; exact ⟨3 * n + 1, main_trans n⟩

end Sz22_2003_unofficial_1589
