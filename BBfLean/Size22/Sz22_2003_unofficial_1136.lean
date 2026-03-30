import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1136: [5/6, 44/35, 49/2, 3/11, 66/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  1  0  0 -1
 1  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1136

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: move e to b.
theorem e_to_b : ∀ k, ⟨(0 : ℕ), b, 0, d, k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm
    exact ih (b := b + 1)

-- R3 chain: move a to d (doubling).
theorem a_to_d : ∀ k, ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

-- R2 chain: (a, 0, k+1, d+k+1, e) →* (a+2*(k+1), 0, 0, d, e+k+1)
theorem r2_chain : ∀ k, ∀ a d e, ⟨a, (0 : ℕ), k + 1, d + k + 1, e⟩ [fm]⊢*
    ⟨a + 2 * (k + 1), 0, 0, d, e + (k + 1)⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · step fm; ring_nf; finish
  · rw [show (k : ℕ) + 1 + 1 = (k + 1) + 1 from rfl,
        show d + (k + 1) + 1 = (d + k + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d (e + 1))
    ring_nf; finish

-- One round of R2, R1, R1.
-- (0, b+2, c+1, d+1, e) → R2 → (2, b+2, c, d, e+1) → R1 → (1, b+1, c+1, d, e+1)
-- → R1 → (0, b, c+2, d, e+1)
theorem r2r1r1_round : ⟨(0 : ℕ), b + 2, c + 1, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 2, d, e + 1⟩ := by
  step fm  -- R2: (2, b+2, c, d, e+1)
  step fm  -- R1: (1, b+1, c+1, d, e+1)
  step fm  -- R1: (0, b, c+2, d, e+1)
  finish

-- R2, R1, R1 interleaved chain: k rounds, each doing R2+R1+R1.
theorem r2r1r1_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), 2 * k, c + 1, d + k, e⟩ [fm]⊢*
    ⟨(0 : ℕ), 0, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    -- (0, 2*k+2, c+1, (d+k)+1, e). Apply r2r1r1_round.
    apply stepStar_trans (r2r1r1_round (b := 2 * k) (c := c) (d := d + k) (e := e))
    -- (0, 2*k, c+2, d+k, e+1) = (0, 2*k, (c+1)+1, d+k, e+1)
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- Main transition.
theorem main_transition (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, n * n + n + 2, 2 * n⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, n * n + 3 * n + 4, 2 * n + 2⟩ := by
  -- Phase 1: e_to_b: (0, 0, 0, D, 2n) →* (0, 2n, 0, D, 0)
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * n) (b := 0) (d := n * n + n + 2))
  rw [show (0 : ℕ) + 2 * n = 2 * n from by ring]
  -- Phase 2: R5 + R1
  rw [show n * n + n + 2 = (n * n + n + 1) + 1 from by ring]
  step fm  -- R5: (1, 2n+1, 0, n²+n+1, 1)
  show ⟨(1 : ℕ), 2 * n + 1, 0, n * n + n + 1, 1⟩ [fm]⊢*
    ⟨0, 0, 0, n * n + 3 * n + 4, 2 * n + 2⟩
  step fm  -- R1: (0, 2n, 1, n²+n+1, 1)
  show ⟨(0 : ℕ), 2 * n, 0 + 1, n * n + n + 1, 1⟩ [fm]⊢*
    ⟨0, 0, 0, n * n + 3 * n + 4, 2 * n + 2⟩
  -- Phase 3: r2r1r1_chain n: (0, 2*n, 0+1, (n²+1)+n, 1) →* (0, 0, 0+n+1, n²+1, 1+n)
  rw [show n * n + n + 1 = (n * n + 1) + n from by ring]
  apply stepStar_trans (r2r1r1_chain n 0 (n * n + 1) 1)
  -- (0, 0, 0+n+1, n²+1, 1+n)
  show ⟨(0 : ℕ), 0, 0 + n + 1, n * n + 1, 1 + n⟩ [fm]⊢*
    ⟨0, 0, 0, n * n + 3 * n + 4, 2 * n + 2⟩
  -- Split n=0 (base) vs n+1 (use r2_chain).
  rcases n with _ | n
  · -- n = 0: (0, 0, 1, 1, 1).
    step fm; step fm; step fm; finish
  · -- n+1: apply r2_chain then a_to_d.
    rw [show (0 : ℕ) + (n + 1) + 1 = (n + 1) + 1 from by ring,
        show 1 + (n + 1) = n + 2 from by ring,
        show (n + 1) * (n + 1) + 1 = n * (n + 1) + (n + 1) + 1 from by ring]
    apply stepStar_trans (r2_chain (n + 1) 0 (n * (n + 1)) (n + 2))
    -- (2*(n+2), 0, 0, n*(n+1), (n+2)+(n+2))
    rw [show 0 + 2 * ((n + 1) + 1) = 2 * n + 4 from by ring,
        show n + 2 + ((n + 1) + 1) = 2 * n + 4 from by ring]
    -- Phase 4: a_to_d
    apply stepStar_trans (a_to_d (2 * n + 4) (d := n * (n + 1)) (e := 2 * n + 4))
    rw [show n * (n + 1) + 2 * (2 * n + 4) = (n + 1) * (n + 1) + 3 * (n + 1) + 4 from by ring,
        show 2 * n + 4 = 2 * (n + 1) + 2 from by ring]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n * n + n + 2, 2 * n⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  rw [show (n + 1) * (n + 1) + (n + 1) + 2 = n * n + 3 * n + 4 from by ring,
      show 2 * (n + 1) = 2 * n + 2 from by ring]
  exact main_transition n
