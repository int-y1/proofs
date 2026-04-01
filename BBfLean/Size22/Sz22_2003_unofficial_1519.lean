import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1519: [7/15, 99/14, 44/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  1
 2 -1  0  0  1
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1519

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: convert e to c (b=0, d=0)
theorem e_to_c : ∀ k, (⟨a, 0, c, 0, e + k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- R3 chain: convert b to a,e (c=0, d=0)
theorem r3_chain : ∀ k, (⟨a, k + b, 0, 0, e⟩ : Q) [fm]⊢* ⟨a + 2 * k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · ring_nf; exists 0
  · rw [show (k + 1) + b = k + (b + 1) from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

-- R2 chain: drain a and d (c=0)
theorem r2_chain : ∀ k, (⟨a + k, b, 0, d + k, e⟩ : Q) [fm]⊢* ⟨a, b + 2 * k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · ring_nf; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 2) (e := e + 1))
    ring_nf; finish

-- Interleaving chain: R1, R2, R1 rounds
-- Each round consumes 1 from a, 2 from c, adds 1 to d and e.
theorem interleave : ∀ C, ∀ A D E, (⟨A + C, 1, 2 * C, D, E⟩ : Q) [fm]⊢* ⟨A, 1, 0, D + C, E + C⟩ := by
  intro C; induction' C with C ih <;> intro A D E
  · ring_nf; exists 0
  · rw [show A + (C + 1) = (A + C) + 1 from by ring,
        show 2 * (C + 1) = (2 * C) + 1 + 1 from by ring]
    step fm  -- R1
    rw [show A + C + 1 = (A + C) + 1 from by ring]
    step fm  -- R2
    rw [show 2 * C + 1 = 2 * C + 0 + 1 from by ring]
    step fm  -- R1
    apply stepStar_trans (ih A (D + 1) (E + 1))
    ring_nf; finish

-- Drain: (A, B+1, 0, D, E) ⊢* (A+2B+3D+2, 0, 0, 0, E+B+3D+1)
-- Total R2 steps = D, total R3 steps = (B+1)+2D.
theorem drain : ∀ D, ∀ A B E, (⟨A, B + 1, 0, D, E⟩ : Q) [fm]⊢*
    ⟨A + 2 * B + 3 * D + 2, 0, 0, 0, E + B + 3 * D + 1⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro A B E
  rcases D with _ | D
  · -- D = 0: R3 chain
    rw [show B + 1 = (B + 1) + 0 from by ring]
    apply stepStar_trans (r3_chain (B + 1) (a := A) (b := 0) (e := E))
    ring_nf; finish
  · -- D + 1: case split on A
    rcases A with _ | A
    · -- A = 0: R3 fires, then R2
      step fm  -- R3: (2, B, 0, D+1, E+1)
      step fm  -- R2: (1, B+2, 0, D, E+2)
      apply stepStar_trans (ih D (by omega) 1 (B + 1) (E + 2))
      ring_nf; finish
    · -- A + 1: R2 fires
      step fm  -- R2: (A, B+3, 0, D, E+1)
      apply stepStar_trans (ih D (by omega) A (B + 2) (E + 1))
      ring_nf; finish

-- Main transition: (C+G+2, 0, 2C+2, 0, 0) ⊢⁺ (3C+G+5, 0, 4C+6, 0, 0)
theorem main_trans (C G : ℕ) :
    (⟨C + G + 2, 0, 2 * C + 2, 0, 0⟩ : Q) [fm]⊢⁺ ⟨3 * C + G + 5, 0, 4 * C + 6, 0, 0⟩ := by
  -- Opening: R5, R1, R2, R1 (4 steps)
  rw [show C + G + 2 = (C + G + 1) + 1 from by ring,
      show 2 * C + 2 = (2 * C) + 1 + 1 from by ring]
  step fm  -- R5: (C+G+1, 1, 2C+2, 0, 1)
  rw [show 2 * C + 1 + 1 = (2 * C) + 1 + 1 from by ring]
  step fm  -- R1: (C+G+1, 0, 2C+1, 1, 1)
  rw [show C + G + 1 = (C + G) + 1 from by ring]
  step fm  -- R2: (C+G, 2, 2C+1, 0, 2)
  rw [show 2 * C + 1 = 2 * C + 0 + 1 from by ring]
  step fm  -- R1: (C+G, 1, 2C, 1, 2)
  -- Interleave: (C+G, 1, 2C, 1, 2) ⊢* (G, 1, 0, C+1, C+2)
  rw [show C + G = G + C from by ring]
  apply stepStar_trans (interleave C G 1 2)
  rw [show 1 + C = C + 1 from by ring, show 2 + C = C + 2 from by ring]
  -- Drain: (G, 1, 0, C+1, C+2) ⊢* (3C+G+5, 0, 0, 0, 4C+6)
  -- drain(C+1, G, 0, C+2) gives (G+2*0+3*(C+1)+2, 0, 0, 0, C+2+0+3*(C+1)+1) = (G+3C+5, 0, 0, 0, 4C+6)
  apply stepStar_trans (drain (C + 1) G 0 (C + 2))
  -- e_to_c: (3C+G+5, 0, 0, 0, 4C+6) ⊢* (3C+G+5, 0, 4C+6, 0, 0)
  rw [show G + 2 * 0 + 3 * (C + 1) + 2 = 3 * C + G + 5 from by ring,
      show C + 2 + 0 + 3 * (C + 1) + 1 = 4 * C + 6 from by ring,
      show (4 * C + 6 : ℕ) = 0 + (4 * C + 6) from by ring]
  apply stepStar_trans (e_to_c (4 * C + 6) (a := 3 * C + G + 5) (c := 0) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + p.2 + 2, 0, 2 * p.1 + 2, 0, 0⟩) ⟨0, 0⟩
  intro ⟨C, G⟩
  refine ⟨⟨2 * C + 2, C + G + 1⟩, ?_⟩
  show (⟨C + G + 2, 0, 2 * C + 2, 0, 0⟩ : Q) [fm]⊢⁺
    ⟨(2 * C + 2) + (C + G + 1) + 2, 0, 2 * (2 * C + 2) + 2, 0, 0⟩
  rw [show (2 * C + 2) + (C + G + 1) + 2 = 3 * C + G + 5 from by ring,
      show 2 * (2 * C + 2) + 2 = 4 * C + 6 from by ring]
  exact main_trans C G

end Sz22_2003_unofficial_1519
