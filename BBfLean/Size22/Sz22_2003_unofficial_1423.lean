import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1423: [7/15, 2/3, 99/14, 5/11, 1089/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  0
-1  2  0 -1  1
 0  0  1  0 -1
-1  2  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1423

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | _ => none

-- R4 repeated: move e to c.
theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- R3+R2×2 repeated: drain d.
theorem drain : ∀ d, ⟨a + 1, 0, 0, d, e⟩ [fm]⊢* ⟨a + 1 + d, 0, 0, 0, e + d⟩ := by
  intro d; induction' d with d ih generalizing a e
  · exists 0
  · step fm; step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

-- Spiral: R3+R1×2 interleaved.
theorem spiral : ∀ c, ⟨c + 1, 0, 2 * c, d + 1, d + 1⟩ [fm]⊢*
    ⟨1, 0, 0, c + d + 1, c + d + 1⟩ := by
  intro c; induction' c with c ih generalizing d
  · simp only [Nat.zero_add, Nat.mul_zero]; exists 0
  · step fm; step fm; step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

-- Main transition: (n+2, 0, 0, 0, 2*(n+1)) ⊢⁺ (n+3, 0, 0, 0, 2*(n+2))
theorem main_trans : ∀ n, ⟨n + 2, 0, 0, 0, 2 * (n + 1)⟩ [fm]⊢⁺
    ⟨n + 3, 0, 0, 0, 2 * (n + 2)⟩ := by
  intro n
  -- e_to_c: convert e to c via R4
  rw [show 2 * (n + 1) = 0 + 2 * (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * (n + 1)))
  rw [show (0 : ℕ) + 2 * (n + 1) = 2 * n + 2 from by ring]
  -- State: (n+2, 0, 2*(n+1), 0, 0). R5 fires.
  step fm
  -- State: (n+1, 2, 2*(n+1), 0, 2). R1 fires.
  step fm
  -- State: (n+1, 1, 2*n+1, 1, 2). R1 fires.
  step fm
  -- State: (n+1, 0, 2*n, 2, 2).
  apply stepStar_trans (spiral n (d := 1))
  show ⟨1, 0, 0, n + 1 + 1, n + 1 + 1⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 2 * (n + 2)⟩
  rw [show n + 1 + 1 = n + 2 from by ring]
  show ⟨0 + 1, 0, 0, n + 2, n + 2⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 2 * (n + 2)⟩
  apply stepStar_trans (drain (n + 2) (a := 0) (e := n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * (n + 1)⟩) 0
  intro n; exists n + 1; exact main_trans n
