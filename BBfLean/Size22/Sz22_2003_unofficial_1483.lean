import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1483: [7/15, 484/3, 99/14, 5/11, 3/2]

Vector representation:
```
 0 -1 -1  1  0
 2 -1  0  0  2
-1  2  0 -1  1
 0  0  1  0 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1483

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: move e to c.
theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- Spiral: drain a while converting c to d and e.
theorem spiral : ∀ k, ⟨k + 1, 0, 2 * k + 1, d + 1, e⟩ [fm]⊢* ⟨1, 0, 1, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · step fm  -- R3
    step fm  -- R1
    step fm  -- R1
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 1) (e := e + 1))
    ring_nf; finish

-- R3+R2+R2 chain: drain d while accumulating a and e.
theorem r3r2r2_chain : ∀ k, ⟨a + 1, 0, 0, d + k, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, d, e + 5 * k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R2
    step fm  -- R2
    apply stepStar_trans (ih (a := a + 3) (e := e + 5))
    ring_nf; finish

-- Spiral closing: (1, 0, 1, d+1, e) ⊢* (2, 0, 0, d+1, e+3)
theorem spiral_close : ⟨1, 0, 1, d + 1, e⟩ [fm]⊢* ⟨2, 0, 0, d + 1, e + 3⟩ := by
  step fm  -- R3
  step fm  -- R1
  step fm  -- R2
  finish

-- Main transition: (n+2, 0, 0, 0, 2*(n+1)) ⊢⁺ (3n+5, 0, 0, 0, 6n+8)
theorem main_trans (n : ℕ) : ⟨n + 2, 0, 0, 0, 2 * (n + 1)⟩ [fm]⊢⁺ ⟨3 * n + 5, 0, 0, 0, 6 * n + 8⟩ := by
  -- e_to_c: move 2*(n+1) from e to c
  have h1 : ⟨n + 2, 0, 0, 0, 2 * (n + 1)⟩ [fm]⊢* ⟨n + 2, 0, 2 * (n + 1), 0, 0⟩ := by
    rw [show 2 * (n + 1) = 0 + (2 * (n + 1)) from by ring]
    exact e_to_c (2 * (n + 1)) (a := n + 2) (c := 0) (e := 0)
  -- R5 step
  have h2 : (fm ⟨n + 2, 0, 2 * (n + 1), 0, 0⟩ = some ⟨n + 1, 1, 2 * (n + 1), 0, 0⟩) := by
    unfold fm; simp
  -- R1 step
  have h3 : (fm ⟨n + 1, 1, 2 * (n + 1), 0, 0⟩ = some ⟨n + 1, 0, 2 * n + 1, 1, 0⟩) := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
    unfold fm; simp
  -- Spiral
  have h4 : ⟨n + 1, 0, 2 * n + 1, 1, 0⟩ [fm]⊢* ⟨1, 0, 1, n + 1, n⟩ := by
    have := spiral n (d := 0) (e := 0)
    simp only [Nat.zero_add] at this
    exact this
  -- Spiral close
  have h5 : ⟨1, 0, 1, n + 1, n⟩ [fm]⊢* ⟨2, 0, 0, n + 1, n + 3⟩ :=
    spiral_close (d := n) (e := n)
  -- R3+R2+R2 chain
  have h6 : ⟨2, 0, 0, n + 1, n + 3⟩ [fm]⊢* ⟨3 * n + 5, 0, 0, 0, 6 * n + 8⟩ := by
    have := r3r2r2_chain (n + 1) (a := 1) (d := 0) (e := n + 3)
    simp only [Nat.zero_add] at this
    rw [show 1 + 3 * (n + 1) + 1 = 3 * n + 5 from by ring,
        show n + 3 + 5 * (n + 1) = 6 * n + 8 from by ring] at this
    exact this
  -- Compose
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2
      (stepStar_trans (step_stepStar h3)
        (stepStar_trans h4 (stepStar_trans h5 h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, 2 * n⟩) 0
  intro n
  rcases n with _ | n
  · exact ⟨1, by execute fm 2⟩
  · refine ⟨3 * n + 4, ?_⟩
    rw [show n + 1 + 1 = n + 2 from by omega,
        show 3 * n + 4 + 1 = 3 * n + 5 from by omega,
        show 2 * (3 * n + 4) = 6 * n + 8 from by ring]
    exact main_trans n
