import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1536: [7/30, 27/35, 22/3, 5/11, 9/2]

Vector representation:
```
-1 -1 -1  1  0
 0  3 -1 -1  0
 1 -1  0  0  1
 0  0  1  0 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1536

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R4+R2+R3x3 loop: each round d-1, a+3, e+2.
theorem main_loop : ∀ n, ∀ A D E,
    ⟨A, 0, 0, D + n, E + 1⟩ [fm]⊢* ⟨A + 3 * n, 0, 0, D, E + 2 * n + 1⟩ := by
  intro n; induction' n with n ih <;> intro A D E
  · exists 0
  · rw [show D + (n + 1) = (D + n) + 1 from by ring]
    -- State: (A, 0, 0, (D+n)+1, E+1)
    step fm  -- R4: (A, 0, 1, (D+n)+1, E)
    step fm  -- R2: (A, 3, 0, D+n, E)
    step fm  -- R3: (A+1, 2, 0, D+n, E+1)
    step fm  -- R3: (A+2, 1, 0, D+n, E+2)
    step fm  -- R3: (A+3, 0, 0, D+n, E+3)
    -- Now: (A+3, 0, 0, D+n, E+3). Need to match (A+3, 0, 0, D+n, (E+2)+1).
    rw [show E + 3 = (E + 2) + 1 from by ring]
    apply stepStar_trans (ih (A + 3) D (E + 2))
    ring_nf; finish

-- R4 chain: transfer e to c.
theorem e_to_c : ∀ k, ∀ A c,
    ⟨A, 0, c, 0, k⟩ [fm]⊢* ⟨A, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A c
  · exists 0
  · step fm
    apply stepStar_trans (ih A (c + 1))
    ring_nf; finish

-- R2+R1x3 chain: each round a-3, c-4, d+2.
theorem r2r1x3_chain : ∀ n, ∀ A D,
    ⟨A + 3 * n, 0, 4 * n, D + 1, 0⟩ [fm]⊢* ⟨A, 0, 0, D + 2 * n + 1, 0⟩ := by
  intro n; induction' n with n ih <;> intro A D
  · simp; exists 0
  · -- State: (A+3n+3, 0, 4n+4, D+1, 0)
    rw [show A + 3 * (n + 1) = A + 3 * n + 3 from by ring,
        show 4 * (n + 1) = 4 * n + 4 from by ring]
    rw [show 4 * n + 4 = (4 * n + 3) + 1 from by ring,
        show D + 1 = D + 1 from rfl]
    step fm  -- R2: (A+3n+3, 3, 4n+3, D, 0)
    rw [show A + 3 * n + 3 = (A + 3 * n + 2) + 1 from by ring,
        show 4 * n + 3 = (4 * n + 2) + 1 from by ring,
        show (3 : ℕ) = 2 + 1 from rfl]
    step fm  -- R1: (A+3n+2, 2, 4n+2, D+1, 0)
    rw [show A + 3 * n + 2 = (A + 3 * n + 1) + 1 from by ring,
        show 4 * n + 2 = (4 * n + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from rfl]
    step fm  -- R1: (A+3n+1, 1, 4n+1, D+2, 0)
    rw [show A + 3 * n + 1 = (A + 3 * n) + 1 from by ring,
        show 4 * n + 1 = (4 * n) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm  -- R1: (A+3n, 0, 4n, D+3, 0)
    rw [show D + 3 = (D + 2) + 1 from by ring]
    apply stepStar_trans (ih A (D + 2))
    ring_nf; finish

-- Main transition: (a+2, 0, 0, 2k+4, 0) ⊢⁺ (a+3k+6, 0, 0, 2k+6, 0)
theorem main_trans (a k : ℕ) :
    ⟨a + 2, 0, 0, 2 * k + 4, 0⟩ [fm]⊢⁺ ⟨a + 3 * k + 6, 0, 0, 2 * k + 6, 0⟩ := by
  -- Opening: R5, R3, R3
  rw [show a + 2 = (a + 1) + 1 from by ring]
  step fm  -- R5: (a+1, 2, 0, 2k+4, 0)
  step fm  -- R3: (a+2, 1, 0, 2k+4, 1)
  step fm  -- R3: (a+3, 0, 0, 2k+4, 2)
  -- Main loop: 2k+4 rounds
  rw [show 2 * k + 4 = 0 + (2 * k + 4) from by ring,
      show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (main_loop (2 * k + 4) (a + 3) 0 1)
  rw [show a + 3 + 3 * (2 * k + 4) = a + 6 * k + 15 from by ring,
      show 1 + 2 * (2 * k + 4) + 1 = 4 * k + 10 from by ring]
  -- State: (a+6k+15, 0, 0, 0, 4k+10)
  apply stepStar_trans (e_to_c (4 * k + 10) (a + 6 * k + 15) 0)
  rw [show 0 + (4 * k + 10) = 4 * k + 10 from by ring]
  -- State: (a+6k+15, 0, 4k+10, 0, 0)
  -- R5+R1x2
  rw [show a + 6 * k + 15 = (a + 6 * k + 14) + 1 from by ring]
  step fm  -- R5: (a+6k+14, 2, 4k+10, 0, 0)
  rw [show a + 6 * k + 14 = (a + 6 * k + 13) + 1 from by ring,
      show 4 * k + 10 = (4 * k + 9) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from rfl]
  step fm  -- R1: (a+6k+13, 1, 4k+9, 1, 0)
  rw [show a + 6 * k + 13 = (a + 6 * k + 12) + 1 from by ring,
      show 4 * k + 9 = (4 * k + 8) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm  -- R1: (a+6k+12, 0, 4k+8, 2, 0)
  -- State: (a+6k+12, 0, 4k+8, 2, 0)
  -- R2+R1x3 chain: k+2 rounds
  rw [show a + 6 * k + 12 = (a + 3 * k + 6) + 3 * (k + 2) from by ring,
      show 4 * k + 8 = 4 * (k + 2) from by ring,
      show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r2r1x3_chain (k + 2) (a + 3 * k + 6) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 4, 0⟩) (by execute fm 46)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, k⟩ ↦ ⟨a + 2, 0, 0, 2 * k + 4, 0⟩) ⟨0, 0⟩
  intro ⟨a, k⟩
  exact ⟨⟨a + 3 * k + 4, k + 1⟩, by
    show ⟨a + 2, 0, 0, 2 * k + 4, 0⟩ [fm]⊢⁺ ⟨a + 3 * k + 4 + 2, 0, 0, 2 * (k + 1) + 4, 0⟩
    rw [show a + 3 * k + 4 + 2 = a + 3 * k + 6 from by ring,
        show 2 * (k + 1) + 4 = 2 * k + 6 from by ring]
    exact main_trans a k⟩

end Sz22_2003_unofficial_1536
