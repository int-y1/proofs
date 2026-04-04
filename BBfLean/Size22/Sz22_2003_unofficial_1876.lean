import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1876: [9/35, 5/198, 14/3, 11/7, 15/2]

Vector representation:
```
 0  2 -1 -1  0
-1 -2  1  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1876

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b+2, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 repeated: move d to e.
theorem d_to_e : ∀ k, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (d := d + 1))
    step fm
    rw [show e + k + 1 = e + (k + 1) from by ring]
    finish

-- One R5+R3+R1+R2 cycle (c >= 1).
theorem one_cycle : ⟨a + 1, 0, c + 1, 0, e + 1⟩ [fm]⊢* ⟨a, 0, c + 2, 0, e⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Drain e, starting from c = 0.
theorem drain_e : ∀ k, ⟨a + k + 1, 0, 0, 0, e + k + 1⟩ [fm]⊢* ⟨a, 0, k + 1, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a e
  · step fm; step fm; step fm; step fm; finish
  · rw [show a + (k + 1) + 1 = (a + 1) + k + 1 from by ring,
        show e + (k + 1) + 1 = (e + 1) + k + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    apply stepStar_trans (one_cycle (a := a) (c := k) (e := e))
    rw [show k + 2 = (k + 1) + 1 from by ring]
    finish

-- R5+R3 opening.
theorem r5_r3 : ⟨a + 1, 0, c, 0, 0⟩ [fm]⊢* ⟨a + 1, 0, c + 1, 1, 0⟩ := by
  step fm; step fm; finish

-- R3+R1 pairs: (a, b+1, c+1, 0, 0) → R3 → (a+1, b, c+1, 1, 0) → R1 → (a+1, b+2, c, 0, 0).
theorem r3_r1_chain : ∀ c, ⟨a, b + 1, c, 0, 0⟩ [fm]⊢* ⟨a + c, b + c + 1, 0, 0, 0⟩ := by
  intro c; induction' c with c ih generalizing a b
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (b := b + 1))
    ring_nf; finish

-- R1 then R3+R1 chain.
theorem r1_r3_chain : ∀ c, ⟨a, 0, c + 1, 1, 0⟩ [fm]⊢* ⟨a + c, c + 2, 0, 0, 0⟩ := by
  intro c
  step fm
  apply stepStar_trans (r3_r1_chain c (a := a) (b := 1))
  ring_nf; finish

-- R3 repeated: drain b to d.
theorem b_to_d : ∀ k, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a + k, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    apply stepStar_trans (ih (b := b + 1))
    step fm
    rw [show d + k + 1 = d + (k + 1) from by ring]
    finish

-- Full transition from (a, 0, 0, d, 0) with d >= 2.
-- Combines all phases into a single ⊢⁺.
theorem full_trans (n : ℕ) :
    ⟨n * n + 3 * n + 3, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨n * n + 5 * n + 7, 0, 0, 2 * n + 4, 0⟩ := by
  -- Take first R4 step to get ⊢⁺
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  -- Remaining d_to_e
  rw [show 2 * n + 1 = 0 + (2 * n + 1) from by ring]
  apply stepStar_trans (d_to_e (k := 2 * n + 1) (a := n * n + 3 * n + 3) (d := 0) (e := 1))
  rw [show 1 + (2 * n + 1) = 2 * n + 2 from by ring]
  -- drain_e
  rw [show n * n + 3 * n + 3 = (n * n + n + 1) + (2 * n + 1) + 1 from by ring,
      show (2 * n + 2 : ℕ) = (0 : ℕ) + (2 * n + 1) + 1 from by ring]
  apply stepStar_trans (drain_e (k := 2 * n + 1) (a := n * n + n + 1) (e := 0))
  -- r5_r3
  rw [show 2 * n + 1 + 1 = 2 * n + 2 from by ring,
      show n * n + n + 1 = (n * n + n) + 1 from by ring]
  apply stepStar_trans (r5_r3 (a := n * n + n) (c := 2 * n + 2))
  -- r1_r3_chain
  rw [show (n * n + n) + 1 = n * n + n + 1 from by ring]
  apply stepStar_trans (r1_r3_chain (2 * n + 2) (a := n * n + n + 1))
  -- b_to_d
  rw [show n * n + n + 1 + (2 * n + 2) = n * n + 3 * n + 3 from by ring,
      show 2 * n + 2 + 2 = 0 + (2 * n + 4) from by ring]
  apply stepStar_trans (b_to_d (k := 2 * n + 4) (a := n * n + 3 * n + 3) (b := 0) (d := 0))
  rw [show 0 + (2 * n + 4) = 2 * n + 4 from by ring,
      show n * n + 3 * n + 3 + (2 * n + 4) = n * n + 5 * n + 7 from by ring]
  finish

-- Base case.
theorem main_trans_zero : ⟨1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨3, 0, 0, 2, 0⟩ := by
  execute fm 5

-- Combined main transition.
theorem main_trans (n : ℕ) :
    ⟨n * n + n + 1, 0, 0, 2 * n, 0⟩ [fm]⊢⁺ ⟨(n + 1) * (n + 1) + (n + 1) + 1, 0, 0, 2 * (n + 1), 0⟩ := by
  rcases n with _ | n
  · exact main_trans_zero
  · show ⟨(n + 1) * (n + 1) + (n + 1) + 1, 0, 0, 2 * (n + 1), 0⟩ [fm]⊢⁺
      ⟨(n + 1 + 1) * (n + 1 + 1) + (n + 1 + 1) + 1, 0, 0, 2 * (n + 1 + 1), 0⟩
    rw [show (n + 1) * (n + 1) + (n + 1) + 1 = n * n + 3 * n + 3 from by ring,
        show 2 * (n + 1) = 2 * n + 2 from by ring,
        show (n + 1 + 1) * (n + 1 + 1) + (n + 1 + 1) + 1 = n * n + 5 * n + 7 from by ring,
        show 2 * (n + 1 + 1) = 2 * n + 4 from by ring]
    exact full_trans n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n * n + n + 1, 0, 0, 2 * n, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
