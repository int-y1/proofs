import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #355: [2/15, 11319/2, 1/3, 25/539, 3/7]

Vector representation:
```
 1 -1 -1  0  0
-1  1  0  3  1
 0 -1  0  0  0
 0  0  2 -2 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_355

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+3, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R2 then R1 loop: each step consumes 1 from c, adds 3 to d and 1 to e
theorem r2r1_loop : ∀ j, ∀ c d e,
    ⟨1, 0, c + j + 1, d, e⟩ [fm]⊢* ⟨1, 0, c + 1, d + 3 * j, e + j⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  rw [show c + (j + 1) + 1 = c + j + 1 + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 loop: convert d,e to c
theorem r4_loop : ∀ j, ∀ c d e,
    ⟨0, 0, c, d + 2 * j, e + j⟩ [fm]⊢* ⟨0, 0, c + 2 * j, d, e⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  rw [show d + 2 * (j + 1) = (d + 2 * j) + 2 from by ring,
      show e + (j + 1) = (e + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Full cycle
theorem main_trans (c d : ℕ) :
    ⟨0, 0, 2 * c + 2, d + 1, 0⟩ [fm]⊢⁺
    ⟨0, 0, 4 * c + 4, d + 2 * c + 2, 0⟩ := by
  -- R5: (0, 0, 2c+2, d+1, 0) -> (0, 1, 2c+2, d, 0)
  -- R1: (0, 1, 2c+2, d, 0) -> (1, 0, 2c+1, d, 0)
  rw [show (2 : ℕ) * c + 2 = 2 * c + 1 + 1 from by ring]
  step fm; step fm
  -- Now at (1, 0, 2c+1, d, 0) which is (1, 0, 0 + (2*c) + 1, d, 0)
  -- R2/R1 loop: 2c iterations
  apply stepStar_trans
  · rw [show 2 * c + 1 = 0 + (2 * c) + 1 from by ring]
    exact r2r1_loop (2 * c) 0 d 0
  -- Now at (1, 0, 1, d + 6c, 2c) which is (1, 0, 0+1, d+3*(2c), 0+2c)
  -- R2: (1, 0, 1, d+6c, 2c) -> (0, 1, 1, d+6c+3, 2c+1)
  -- R1: (0, 1, 1, d+6c+3, 2c+1) -> (1, 0, 0, d+6c+3, 2c+1)
  -- R2: (1, 0, 0, d+6c+3, 2c+1) -> (0, 1, 0, d+6c+6, 2c+2)
  -- R3: (0, 1, 0, d+6c+6, 2c+2) -> (0, 0, 0, d+6c+6, 2c+2)
  step fm; step fm; step fm; step fm
  -- Now at (0, 0, 0, d+6c+6, 2c+2)
  -- R4 loop: 2c+2 times
  -- Need: (0, 0, 0, (d+2c+2) + 2*(2c+2), 0 + (2c+2)) ->* (0, 0, 4c+4, d+2c+2, 0)
  apply stepStar_trans
  · have h := r4_loop (2 * c + 2) 0 (d + 2 * c + 2) 0
    rw [show (d + 2 * c + 2) + 2 * (2 * c + 2) = d + 3 * (2 * c) + 3 + 3 from by ring,
        show 0 + (2 * c + 2) = 0 + 2 * c + 1 + 1 from by ring,
        show 0 + 2 * (2 * c + 2) = 4 * c + 4 from by ring] at h
    exact h
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 8, 5, 0⟩) (by execute fm 25)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 2 * p.1 + 2, p.2 + 1, 0⟩) ⟨3, 4⟩
  intro ⟨c, d⟩
  exact ⟨⟨2 * c + 1, d + 2 * c + 1⟩, by
    show ⟨0, 0, 2 * c + 2, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * (2 * c + 1) + 2, (d + 2 * c + 1) + 1, 0⟩
    rw [show 2 * (2 * c + 1) + 2 = 4 * c + 4 from by ring,
        show (d + 2 * c + 1) + 1 = d + 2 * c + 2 from by ring]
    exact main_trans c d⟩

end Sz22_2003_unofficial_355
