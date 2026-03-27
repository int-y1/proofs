import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #594: [35/6, 121/2, 28/55, 3/7, 6/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  1 -1
 0  1  0 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_594

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (h _); ring_nf; finish
  exact many_step k b

-- R5 + R1: opening two steps
theorem opening : ⟨0, B, 0, 0, E + 1⟩ [fm]⊢⁺ ⟨0, B, 1, 1, E⟩ := by
  step fm; step fm; ring_nf; finish

-- R3R1R1 chain: (0, 2k, C+1, D, C+2k+1) ->* (0, 0, C+k+1, D+3k, C+k+1)
theorem r3r1r1_chain :
    ∀ k C D, ⟨0, 2*k, C+1, D, C+2*k+1⟩ [fm]⊢* ⟨0, 0, C+k+1, D+3*k, C+k+1⟩ := by
  intro k; induction' k with k h <;> intro C D
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
      show C + (2 * k + 2) + 1 = (C + 2 * k + 1) + 2 from by ring]
  step fm; step fm; step fm
  rw [show C + 2 * k + 1 + 1 = (C + 1) + 2 * k + 1 from by ring]
  apply stepStar_trans (h (C + 1) (D + 3))
  ring_nf; finish

-- R3R2R2 chain: (0, 0, c+k, d, e+k) ->* (0, 0, c, d+k, e+4*k)
theorem r3r2r2_chain :
    ∀ k, ∀ c d e, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e+4*k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + k + 4 = (e + 4) + k from by ring]
  apply stepStar_trans (h c (d + 1) (e + 4))
  ring_nf; finish

-- Main transition: (0, 0, 0, 2n, 2n+2) ->+ (0, 0, 0, 4n+2, 4n+4)
theorem main_trans (n : ℕ) : ⟨0, 0, 0, 2*n, 2*n+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*n+2, 4*n+4⟩ := by
  -- Phase A: d_to_b: (0,0,0,2n,2n+2) -> (0,2n,0,0,2n+2)
  have hA := @d_to_b (0 : ℕ) 0 (2*n) (2*n+2)
  rw [Nat.zero_add] at hA
  apply stepStar_stepPlus_stepPlus hA
  -- Phase B: opening: (0,2n,0,0,2n+2) -> (0,2n,1,1,2n+1)
  rw [show 2*n+2 = (2*n+1)+1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (B := 2*n) (E := 2*n+1))
  -- Phase C: r3r1r1_chain: (0,2n,1,1,2n+1) -> (0,0,n+1,3n+1,n+1)
  rw [show 2*n+1 = 0 + 2*n + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain n 0 1)
  rw [Nat.zero_add]
  -- Phase D: r3r2r2_chain: (0,0,n+1,3n+1,n+1) -> (0,0,0,4n+2,4n+4)
  have hD := r3r2r2_chain (n+1) 0 (3*n+1) 0
  rw [Nat.zero_add, Nat.zero_add] at hD
  rw [show 1 + 3 * n = 3 * n + 1 from by ring]
  apply stepStar_trans hD
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n, 2 * n + 2⟩) 0
  intro n; exists 2 * n + 1
  rw [show (⟨0, 0, 0, 2 * (2 * n + 1), 2 * (2 * n + 1) + 2⟩ : Q) =
      ⟨0, 0, 0, 4 * n + 2, 4 * n + 4⟩ from by ring_nf]
  exact main_trans n

end Sz22_2003_unofficial_594
