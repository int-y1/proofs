import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1494: [7/15, 9/385, 242/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2 -1 -1 -1
 1 -1  0  0  2
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1494

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: transfer e to c.
theorem e_to_c : ∀ k c, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c; exists 0
  · intro c; rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih (c + 1)); ring_nf; finish

-- Upward micro-cycle: R4, R2, R3, R3.
theorem upward_loop : ∀ k : ℕ, ∀ a d e, ⟨a, 0, 0, d + k, e + 2⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e + 2 * k + 2⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (a + 2) d (e + 2))
    ring_nf; finish

-- Downward 5-step cycle: R5, R1, R2, R1, R1.
theorem downward_loop : ∀ k a c d, ⟨a + k, 0, c + 4 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro a c d; exists 0
  · intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 4 * (k + 1) = (c + 4 * k) + 4 from by ring]
    step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 2))
    ring_nf; finish

-- Remainder c=3: 5 steps R5, R1, R2, R1, R3.
theorem remainder3 : ⟨a + 1, 0, 3, d, 0⟩ [fm]⊢* ⟨a + 1, 0, 0, d + 1, 2⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Main transition.
theorem main_trans (n : ℕ) :
    ⟨3 * n ^ 2 + 4 * n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺
    ⟨3 * n ^ 2 + 10 * n + 9, 0, 0, 2 * n + 4, 0⟩ := by
  -- Phase 1: R5, R3
  step fm; step fm
  -- Phase 2: Upward loop x(2n+2)
  have h2 := upward_loop (2 * n + 2) (3 * n ^ 2 + 4 * n + 2) 0 1
  rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring,
      show 1 + 2 = 3 from by ring,
      show 3 * n ^ 2 + 4 * n + 2 + 2 * (2 * n + 2) = 3 * n ^ 2 + 8 * n + 6 from by ring,
      show 1 + 2 * (2 * n + 2) + 2 = 4 * n + 7 from by ring] at h2
  apply stepStar_trans h2
  -- Phase 3: R4 chain
  have h3 := e_to_c (4 * n + 7) 0 (a := 3 * n ^ 2 + 8 * n + 6) (e := 0)
  rw [show (0 : ℕ) + (4 * n + 7) = 4 * n + 7 from by ring] at h3
  apply stepStar_trans h3
  -- Phase 4: Downward loop x(n+1)
  have h4 := downward_loop (n + 1) (3 * n ^ 2 + 7 * n + 5) 3 0
  rw [show (3 * n ^ 2 + 7 * n + 5) + (n + 1) = 3 * n ^ 2 + 8 * n + 6 from by ring,
      show 3 + 4 * (n + 1) = 4 * n + 7 from by ring,
      show 0 + 2 * (n + 1) = 2 * n + 2 from by ring] at h4
  apply stepStar_trans h4
  -- Phase 5: Remainder c=3
  have h5 := remainder3 (a := 3 * n ^ 2 + 7 * n + 4) (d := 2 * n + 2)
  rw [show 3 * n ^ 2 + 7 * n + 4 + 1 = 3 * n ^ 2 + 7 * n + 5 from by ring] at h5
  apply stepStar_trans h5
  -- Phase 6: Upward loop x(2n+3)
  have h6 := upward_loop (2 * n + 3) (3 * n ^ 2 + 7 * n + 5) 0 0
  rw [show 0 + (2 * n + 3) = 2 * n + 3 from by ring,
      show 0 + 2 = 2 from by ring,
      show 3 * n ^ 2 + 7 * n + 5 + 2 * (2 * n + 3) = 3 * n ^ 2 + 11 * n + 11 from by ring,
      show 0 + 2 * (2 * n + 3) + 2 = 4 * n + 8 from by ring] at h6
  rw [show (2 * n + 2 + 1 : ℕ) = 2 * n + 3 from by ring]
  apply stepStar_trans h6
  -- Phase 7: R4 chain
  have h7 := e_to_c (4 * n + 8) 0 (a := 3 * n ^ 2 + 11 * n + 11) (e := 0)
  rw [show (0 : ℕ) + (4 * n + 8) = 4 * n + 8 from by ring] at h7
  apply stepStar_trans h7
  -- Phase 8: Downward loop x(n+2)
  have h8 := downward_loop (n + 2) (3 * n ^ 2 + 10 * n + 9) 0 0
  rw [show (3 * n ^ 2 + 10 * n + 9) + (n + 2) = 3 * n ^ 2 + 11 * n + 11 from by ring,
      show 0 + 4 * (n + 2) = 4 * n + 8 from by ring,
      show 0 + 2 * (n + 2) = 2 * n + 4 from by ring] at h8
  exact h8

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩)
  · execute fm 23
  · have key : ¬halts fm (⟨3 * 0 ^ 2 + 4 * 0 + 2, 0, 0, 2 * 0 + 2, 0⟩ : Q) := by
      apply progress_nonhalt_simple (fm := fm) (A := ℕ)
        (fun n ↦ ⟨3 * n ^ 2 + 4 * n + 2, 0, 0, 2 * n + 2, 0⟩) 0
      intro n; exact ⟨n + 1, by
        rw [show 3 * (n + 1) ^ 2 + 4 * (n + 1) + 2 = 3 * n ^ 2 + 10 * n + 9 from by ring,
            show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
        exact main_trans n⟩
    simp at key; exact key

end Sz22_2003_unofficial_1494
