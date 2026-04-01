import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1418: [7/15, 132/7, 1/3, 25/2, 1/55, 3/5]

Vector representation:
```
 0 -1 -1  1  0
 2  1  0 -1  1
 0 -1  0  0  0
-1  0  2  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1418

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1+R2 alternating chain: k rounds of (R1, R2).
-- From (a, 1, k, 0, e) to (a+2k, 1, 0, 0, e+k).
theorem r1r2_chain : ∀ k, ∀ a e, ⟨a, 1, k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 1, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 2) (e + 1)); ring_nf; finish

-- R4 chain: convert a to c.
theorem r4_chain : ∀ k c, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 2)); ring_nf; finish

-- R5 chain: subtract from both c and e.
theorem r5_chain : ∀ k c, ⟨0, 0, c + k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c); ring_nf; finish

-- Main transition: (0, 0, n+2, 0, 0) ⊢⁺ (0, 0, 3n+3, 0, 0).
theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * n + 3, 0, 0⟩ := by
  rw [show n + 2 = (n + 1) + 1 from by ring]
  -- R6: (0, 0, (n+1)+1, 0, 0) -> (0, 1, n+1, 0, 0)
  step fm
  -- R1+R2 chain: (0, 1, n+1, 0, 0) -> (2(n+1), 1, 0, 0, n+1)
  apply stepStar_trans (r1r2_chain (n + 1) 0 0)
  rw [show 0 + 2 * (n + 1) = 2 * (n + 1) from by ring,
      show 0 + (n + 1) = n + 1 from by ring]
  -- R3: (2(n+1), 1, 0, 0, n+1) -> (2(n+1), 0, 0, 0, n+1)
  step fm
  -- R4 chain: (2(n+1), 0, 0, 0, n+1) -> (0, 0, 4(n+1), 0, n+1)
  apply stepStar_trans (r4_chain (2 * (n + 1)) 0 (e := n + 1))
  rw [show 0 + 2 * (2 * (n + 1)) = 3 * (n + 1) + (n + 1) from by ring]
  -- R5 chain: (0, 0, 3(n+1)+(n+1), 0, n+1) -> (0, 0, 3(n+1), 0, 0)
  apply stepStar_trans (r5_chain (n + 1) (3 * (n + 1)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 0, 0⟩) 0
  intro n; exact ⟨3 * n + 1, main_trans n⟩

end Sz22_2003_unofficial_1418
