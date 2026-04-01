import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1201: [5/6, 539/2, 4/35, 3/11, 1/5, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  0
 0  1  0  0 -1
 0  0 -1  0  0
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1201

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move e to b. (0, b, 0, d, e+k) →* (0, b+k, 0, d, e)
theorem e_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R6 then R3: (0, b, 0, d+2, 0) →⁺ (2, b, 0, d, 0)
theorem r6_r3 : ⟨(0 : ℕ), b, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨(2 : ℕ), b, 0, d, 0⟩ := by
  step fm; step fm; finish

-- R1,R1,R3 loop: (2, b+2*k, c, d+k, 0) →* (2, b, c+k, d, 0)
theorem r1r1r3_loop : ∀ k b c d, ⟨(2 : ℕ), b + 2 * k, c, d + k, 0⟩ [fm]⊢* ⟨(2 : ℕ), b, c + k, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro b c d; exists 0
  · intro b c d
    rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1))
    rw [show c + k = c + k from rfl]
    step fm; step fm; step fm
    ring_nf; finish

-- R3,R2,R2 loop: (0, 0, c+k, d+1, e) →* (0, 0, c, d+1+3*k, e+2*k)
theorem r3r2r2_loop : ∀ k c d e, ⟨(0 : ℕ), 0, c + k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + 1 + 3 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro c d e; exists 0
  · intro c d e
    rw [show c + (k + 1) = c + k + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm  -- R3: (2, 0, c+k, d, e)
    step fm  -- R2: (1, 0, c+k, d+2, e+1)
    step fm  -- R2: (0, 0, c+k, d+4, e+2)
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 2))
    ring_nf; finish

-- Main transition: (0, 0, 0, n*n+2*n+2, 2*n+1) →⁺ (0, 0, 0, n*n+4*n+5, 2*n+3)
theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, n * n + 2 * n + 2, 2 * n + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, n * n + 4 * n + 5, 2 * n + 3⟩ := by
  -- Phase 1: R4 x (2n+1): e->b
  rw [show (2 * n + 1 : ℕ) = 0 + (2 * n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * n + 1) 0 (n * n + 2 * n + 2) 0)
  rw [show (0 : ℕ) + (2 * n + 1) = 2 * n + 1 from by ring]
  -- Phase 2+3: R6, R3
  rw [show n * n + 2 * n + 2 = (n * n + 2 * n) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus r6_r3
  -- Phase 4: R1,R1,R3 x n
  rw [show 2 * n + 1 = 1 + 2 * n from by ring,
      show n * n + 2 * n = (n * n + n) + n from by ring]
  apply stepStar_trans (r1r1r3_loop n 1 0 (n * n + n))
  rw [show (0 : ℕ) + n = n from by ring]
  -- Phase 5: R1
  step fm
  -- Phase 6: R2
  step fm
  -- Phase 7: R3,R2,R2 x (n+1)
  rw [show n + 1 = 0 + (n + 1) from by ring,
      show n * n + n + 2 = (n * n + n + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_loop (n + 1) 0 (n * n + n + 1) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n * n + 2 * n + 2, 2 * n + 1⟩) 0
  intro n; exists n + 1
  rw [show (n + 1) * (n + 1) + 2 * (n + 1) + 2 = n * n + 4 * n + 5 from by ring,
      show 2 * (n + 1) + 1 = 2 * n + 3 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1201
