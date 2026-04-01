import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1533: [7/30, 22/3, 27/35, 5/11, 9/2]

Vector representation:
```
-1 -1 -1  1  0
 1 -1  0  0  1
 0  3 -1 -1  0
 0  0  1  0 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1533

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- (R4, R3, R2, R2, R2) x n: drain d.
theorem drain_d : ∀ n, ∀ A e,
    ⟨A, 0, 0, n, e + 1⟩ [fm]⊢* ⟨A + 3 * n, 0, 0, 0, e + 1 + 2 * n⟩ := by
  intro n; induction' n with n ih <;> intro A e
  · exists 0
  · step fm; step fm  -- R4, R3
    rw [show (3 : ℕ) = 2 + 1 from rfl]
    step fm; step fm; step fm  -- R2 x3
    rw [show A + 1 + 1 + 1 = A + 3 from by ring,
        show e + 1 + 1 + 1 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih (A + 3) (e + 2))
    ring_nf; finish

-- R4 x n: transfer e to c.
theorem e_to_c : ∀ n A c,
    ⟨A, 0, c, 0, n⟩ [fm]⊢* ⟨A, 0, c + n, 0, 0⟩ := by
  intro n; induction' n with n ih <;> intro A c
  · exists 0
  · step fm
    apply stepStar_trans (ih A (c + 1))
    ring_nf; finish

-- (R3, R1, R1, R1) x n: drain a and c, build d.
theorem r3r1_chain : ∀ n, ∀ A D,
    ⟨A + 3 * n, 0, 4 * n, D + 1, 0⟩ [fm]⊢* ⟨A, 0, 0, D + 2 * n + 1, 0⟩ := by
  intro n; induction' n with n ih <;> intro A D
  · exists 0
  · rw [show A + 3 * (n + 1) = A + 3 * n + 2 + 1 from by ring,
        show 4 * (n + 1) = (4 * n + 3) + 1 from by ring]
    step fm  -- R3
    rw [show (3 : ℕ) = 2 + 1 from rfl,
        show 4 * n + 3 = (4 * n + 2) + 1 from by ring]
    step fm  -- R1
    rw [show A + 3 * n + 2 = (A + 3 * n + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from rfl,
        show 4 * n + 2 = (4 * n + 1) + 1 from by ring]
    step fm  -- R1
    rw [show A + 3 * n + 1 = (A + 3 * n) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl,
        show 4 * n + 1 = (4 * n) + 1 from by ring]
    step fm  -- R1
    rw [show D + 1 + 1 + 1 = (D + 2) + 1 from by ring]
    apply stepStar_trans (ih A (D + 2))
    ring_nf; finish

-- Main transition
theorem main_trans (a k : ℕ) :
    ⟨a + 1, 0, 0, 2 * k + 4, 0⟩ [fm]⊢⁺ ⟨a + 3 * k + 5, 0, 0, 2 * k + 6, 0⟩ := by
  -- Phase 1: R5, R2, R2
  step fm  -- R5: -> (a, 2, 0, 2k+4, 0)
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm  -- R2: -> (a+1, 1, 0, 2k+4, 1)
  step fm  -- R2: -> (a+2, 0, 0, 2k+4, 2)
  rw [show (2 : ℕ) = (1 : ℕ) + 1 from rfl]
  -- Phase 2: drain d
  apply stepStar_trans (drain_d (2 * k + 4) (a + 2) 1)
  rw [show a + 2 + 3 * (2 * k + 4) = a + 6 * k + 14 from by ring,
      show 1 + 1 + 2 * (2 * k + 4) = 4 * k + 10 from by ring]
  -- Phase 3: e to c
  apply stepStar_trans (e_to_c (4 * k + 10) (a + 6 * k + 14) 0)
  rw [show 0 + (4 * k + 10) = 4 * k + 10 from by ring]
  -- State: (a+6k+14, 0, 4k+10, 0, 0)
  -- Phase 4: R5, R1, R1
  rw [show a + 6 * k + 14 = (a + 6 * k + 13) + 1 from by ring,
      show 4 * k + 10 = (4 * k + 9) + 1 from by ring]
  step fm  -- R5
  rw [show a + 6 * k + 13 = (a + 6 * k + 12) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from rfl,
      show 4 * k + 10 = (4 * k + 9) + 1 from by ring]
  step fm  -- R1
  rw [show a + 6 * k + 12 = (a + 6 * k + 11) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl,
      show 4 * k + 9 = (4 * k + 8) + 1 from by ring]
  step fm  -- R1
  -- Phase 5: r3r1_chain
  rw [show a + 6 * k + 11 = (a + 3 * k + 5) + 3 * (k + 2) from by ring,
      show 4 * k + 8 = 4 * (k + 2) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r1_chain (k + 2) (a + 3 * k + 5) 1)
  rw [show 1 + 2 * (k + 2) + 1 = 2 * k + 6 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 4, 0⟩) (by execute fm 46)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, k⟩ ↦ ⟨a + 1, 0, 0, 2 * k + 4, 0⟩) ⟨1, 0⟩
  intro ⟨a, k⟩; exact ⟨⟨a + 3 * k + 4, k + 1⟩, main_trans a k⟩

end Sz22_2003_unofficial_1533
