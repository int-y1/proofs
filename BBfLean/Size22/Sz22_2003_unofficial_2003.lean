import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #2003: [99/70, 7/15, 22/3, 5/11, 21/2]

Vector representation:
```
-1  2 -1 -1  1
 0 -1 -1  1  0
 1 -1  0  0  1
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_2003

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ⟨0, b + k, c + k, d, e⟩ [fm]⊢* ⟨0, b, c, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r2_drain : ∀ k, ⟨0, k + 1, k, d, e⟩ [fm]⊢* ⟨0, 1, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem pair_step : ⟨a + 1, b, c + 2, 1, e⟩ [fm]⊢* ⟨a, b + 1, c, 1, e + 1⟩ := by
  step fm; step fm; finish

theorem pair_chain : ∀ k, ∀ b c e, ⟨a + k, b, c + 2 * k, 1, e⟩ [fm]⊢* ⟨a, b + k, c, 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    apply stepStar_trans (pair_step (a := a + k) (b := b) (c := c + 2 * k) (e := e))
    apply stepStar_trans (ih (b := b + 1) (c := c) (e := e + 1))
    ring_nf; finish

theorem spiral_round : ⟨a + 1, 0, 0, d + 1, e + 1⟩ [fm]⊢* ⟨a + 2, 0, 0, d, e + 3⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem spiral : ∀ k, ⟨a + 1, 0, 0, k, e + 1⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · apply stepStar_trans (spiral_round (a := a) (d := k) (e := e))
    rw [show a + 2 = (a + 1) + 1 from by ring,
        show e + 3 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (e := e + 2))
    ring_nf; finish

theorem main_trans : ∀ n, ⟨n + 2, 0, 0, 0, 3 * n + 3⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 3 * n + 6⟩ := by
  intro n
  -- Phase 1: e_to_c
  rw [show (3 * n + 3 : ℕ) = 0 + (3 * n + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (3 * n + 3) (a := n + 2) (c := 0) (e := 0))
  -- Now at (n+2, 0, 0+(3n+3), 0, 0). R5 step gives ⊢⁺.
  rw [show 0 + (3 * n + 3) = 3 * n + 3 from by ring,
      show (n + 2 : ℕ) = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(n + 1) + 1, 0, 3 * n + 3, 0, 0⟩ = some ⟨n + 1, 1, 3 * n + 3, 1, 0⟩
    simp [fm]
  -- Now at (n+1, 1, 3n+3, 1, 0). Pair chain.
  show ⟨n + 1, 1, 3 * n + 3, 1, 0⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 3 * n + 6⟩
  rw [show (3 * n + 3 : ℕ) = (n + 3) + 2 * n from by ring,
      show (n + 1 : ℕ) = 1 + n from by ring]
  apply stepStar_trans (pair_chain n (a := 1) (b := 1) (c := n + 3) (e := 0))
  -- Now at (1, 1+n, n+3, 1, 0+n). Final R1.
  rw [show 1 + n = n + 1 from by ring,
      show (n + 3 : ℕ) = (n + 2) + 1 from by ring,
      show 0 + n = n from by ring]
  apply stepStar_trans
  · show ⟨1, n + 1, (n + 2) + 1, 1, n⟩ [fm]⊢* ⟨0, n + 1 + 2, n + 2, 0, n + 1⟩
    step fm; finish
  -- Now at (0, n+3, n+2, 0, n+1). R2 chain.
  rw [show n + 1 + 2 = (n + 2) + 1 from by ring]
  apply stepStar_trans (r2_drain (n + 2) (d := 0) (e := n + 1))
  -- Now at (0, 1, 0, 0+(n+2), n+1). R3 + spiral.
  simp only [Nat.zero_add]
  step fm
  -- Now at (1, 0, 0, n+2, n+2). Spiral.
  rw [show (n + 2 : ℕ) = (n + 1) + 1 from by ring]
  apply stepStar_trans (spiral (n + 2) (a := 0) (e := n + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 3 * n + 3⟩) 0
  intro n; exists n + 1
  exact main_trans n
