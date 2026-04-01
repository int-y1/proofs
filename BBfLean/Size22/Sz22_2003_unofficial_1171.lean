import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1171: [5/6, 49/2, 44/245, 3/11, 22/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -2  1
 0  1  0  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1171

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+2, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R4 chain: move e to b
theorem e_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show b + (k + 1) = (b + 1) + k from by ring]
    exact ih (b + 1) d e

-- R3,R2,R2 chain: drain c, d increases by 2 each round
theorem r3r2r2_chain : ∀ C, ∀ D E,
    ⟨0, 0, C + 1, D + 2, E⟩ [fm]⊢* ⟨0, 0, 0, D + 2 * C + 4, E + C + 1⟩ := by
  intro C; induction' C with C ih <;> intro D E
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show C + 1 + 1 = (C + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show D + 2 * (C + 1) + 4 = (D + 2) + 2 * C + 4 from by ring,
        show E + (C + 1) + 1 = (E + 1) + C + 1 from by ring,
        show D + 2 + 2 = (D + 2) + 2 from by ring]
    exact ih (D + 2) (E + 1)

-- R3,R1,R2 step for b=1
theorem b1_step : ∀ C D E,
    ⟨0, 1, C + 1, D + 2, E⟩ [fm]⊢* ⟨0, 0, C + 1, D + 2, E + 1⟩ := by
  intro C D E; step fm; step fm; step fm; finish

-- Middle phase: from (0, B, C+1, B+D+2, E) to (0, 0, 0, B+D+2C+4, E+B+C+1)
theorem middle : ∀ B, ∀ C D E,
    ⟨0, B, C + 1, B + D + 2, E⟩ [fm]⊢* ⟨0, 0, 0, B + D + 2 * C + 4, E + B + C + 1⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro C D E
  rcases B with _ | _ | B
  · -- B = 0
    simp only [Nat.zero_add]
    exact r3r2r2_chain C D E
  · -- B = 1
    rw [show 1 + D + 2 = (D + 1) + 2 from by ring]
    apply stepStar_trans (b1_step C (D + 1) E)
    rw [show 1 + D + 2 * C + 4 = (D + 1) + 2 * C + 4 from by ring,
        show E + 1 + C + 1 = (E + 1) + C + 1 from by ring]
    exact r3r2r2_chain C (D + 1) (E + 1)
  · -- B + 2
    rw [show B + 2 + D + 2 = (B + D + 2) + 2 from by ring]
    step fm; step fm; step fm
    rw [show B + 2 + D + 2 * C + 4 = B + D + 2 * (C + 1) + 4 from by ring,
        show E + (B + 2) + C + 1 = (E + 1) + B + (C + 1) + 1 from by ring,
        show C + 1 + 1 = (C + 1) + 1 from by ring]
    exact ih B (by omega) (C + 1) D (E + 1)

-- R5 step: (0, b, 0, d+1, 0) => (1, b, 0, d, 1)
theorem r5_step : ∀ b d, ⟨0, b, 0, d + 1, 0⟩ [fm]⊢ ⟨1, b, 0, d, 1⟩ := by
  intro b d; unfold fm; simp

-- R1 step: (1, b+1, c, d, e) => (0, b, c+1, d, e)
theorem r1_step : ∀ b c d e, ⟨1, b + 1, c, d, e⟩ [fm]⊢ ⟨0, b, c + 1, d, e⟩ := by
  intro b c d e; unfold fm; simp

-- Full transition: (0,0,0,n+2,n) =>+ (0,0,0,n+3,n+1)
theorem transition : ∀ n, ⟨0, 0, 0, n + 2, n⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 3, n + 1⟩ := by
  intro n
  rcases n with _ | n
  · execute fm 2
  · -- n + 1 >= 1
    -- Phase 1: R4 chain
    apply stepStar_stepPlus_stepPlus
    · rw [show n + 1 + 2 = n + 3 from by ring,
          show (n + 1 : ℕ) = 0 + (n + 1) from by ring]
      exact e_to_b (n + 1) 0 (n + 3) 0
    -- Now at (0, n+1, 0, n+3, 0)
    rw [show 0 + (n + 1) = n + 1 from by ring,
        show n + 3 = (n + 2) + 1 from by ring]
    -- R5
    apply step_stepPlus_stepPlus (r5_step (n + 1) (n + 2))
    -- Now at (1, n+1, 0, n+2, 1)
    -- R1
    apply step_stepStar_stepPlus (r1_step n 0 (n + 2) 1)
    -- Now at (0, n, 0+1, n+2, 1). Apply middle with B=n, C=0, D=0, E=1.
    have h := middle n 0 0 1
    simp only [Nat.zero_add, Nat.add_zero, Nat.mul_zero] at h
    rw [show (1 : ℕ) + n + 1 = n + 2 from by ring] at h
    rw [show n + 1 + 3 = n + 4 from by ring,
        show n + 1 + 1 = n + 2 from by ring]
    simp only [Nat.zero_add]
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, n⟩) 0
  intro n; exact ⟨n + 1, transition n⟩

end Sz22_2003_unofficial_1171
