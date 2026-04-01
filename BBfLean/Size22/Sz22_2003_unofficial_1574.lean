import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1574: [7/45, 275/14, 6/5, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  0
-1  0  2 -1  1
 1  1 -1  0  0
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1574

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- Ramp-up: R1,R2,R3,R3 repeated.
theorem rampup : ∀ k j e, ⟨j + 2, 2, k, 0, e⟩ [fm]⊢* ⟨j + k + 2, 2, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro j e
  · exists 0
  · step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (j + 1) (e + 1)); ring_nf; finish

-- R4 transfer: e to b.
theorem e_to_b : ∀ k a b, ⟨a, b, 0, 0, e + k⟩ [fm]⊢* ⟨a, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih a (b + 1)); ring_nf; finish

-- Drain: (a+1, 4*a+2, 0, d+1, e) -> (0, 0, 1, d+a+1, e+a+1).
-- Uses d+1 encoding since R2 needs d >= 1.
theorem drain : ∀ a d e, ⟨a + 1, 4 * a + 2, 0, d + 1, e⟩ [fm]⊢* ⟨0, 0, 1, d + a + 1, e + a + 1⟩ := by
  intro a; induction' a with a ih <;> intro d e
  · step fm; step fm; ring_nf; finish
  · rw [show 4 * (a + 1) + 2 = (4 * a + 2) + 4 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (d + 1) (e + 1)); ring_nf; finish

-- Interleaved chain: R3,R2,R3,R1,R2 repeated.
-- Uses d+1 encoding since R2 needs d >= 1.
theorem interleave : ∀ k c e, ⟨0, 0, c + 1, k + 1, e⟩ [fm]⊢* ⟨0, 0, c + k + 2, 0, e + 2 * k + 2⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · step fm; step fm; step fm; step fm; step fm; ring_nf; finish
  · step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (e + 2)); ring_nf; finish

-- Main transition: (0, 0, n+2, 0, 3*n+2) ⊢⁺ (0, 0, n+3, 0, 3*n+5).
theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 2, 0, 3 * n + 2⟩ [fm]⊢⁺ ⟨0, 0, n + 3, 0, 3 * n + 5⟩ := by
  -- R3, R3: -> (2, 2, n, 0, 3n+2)
  rw [show n + 2 = n + 1 + 1 from by ring]
  step fm; step fm
  -- Ramp-up: (2, 2, n, 0, 3n+2) -> (n+2, 2, 0, 0, 4n+2)
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (rampup n 0 (3 * n + 2))
  rw [show 0 + n + 2 = n + 2 from by ring,
      show 3 * n + 2 + n = 0 + (4 * n + 2) from by ring]
  -- R4 transfer: (n+2, 2, 0, 0, 4n+2) -> (n+2, 4n+4, 0, 0, 0)
  apply stepStar_trans (e_to_b (4 * n + 2) (n + 2) 2 (e := 0))
  rw [show 2 + (4 * n + 2) = 4 * n + 4 from by ring]
  -- R5, R1: (n+2, 4n+4, 0, 0, 0) -> (n+1, 4n+2, 0, 2, 0)
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show 4 * n + 4 = (4 * n + 2) + 2 from by ring]
  step fm; step fm
  -- Drain: (n+1, 4n+2, 0, 2, 0) -> (0, 0, 1, n+2, n+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (drain n 1 0)
  rw [show 1 + n + 1 = n + 2 from by ring,
      show 0 + n + 1 = n + 1 from by ring]
  -- Interleave: (0, 0, 1, n+2, n+1) -> (0, 0, n+3, 0, 3n+5)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply stepStar_trans (interleave (n + 1) 0 (n + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 0, 3 * n + 2⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1574
