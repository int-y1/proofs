import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1061: [5/18, 77/2, 44/35, 3/11, 10/7]

Vector representation:
```
-1 -2  1  0  0
-1  0  0  1  1
 2  0 -1 -1  1
 0  1  0  0 -1
 1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1061

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

private theorem r3_drain : ∀ k, ∀ b D,
    ⟨(0 : ℕ), b, 0, D, k⟩ [fm]⊢* ⟨0, b + k, 0, D, 0⟩ := by
  intro k; induction' k with k ih <;> intro b D
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) D

private theorem inner_loop : ∀ k, ∀ D E,
    ⟨(0 : ℕ), 1, k, D + 1, E⟩ [fm]⊢* ⟨0, 1, 0, D + 1 + k, E + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro D E
  · ring_nf; finish
  · rw [show D + 1 + (k + 1) = (D + 1) + 1 + k from by ring,
        show E + 3 * (k + 1) = (E + 3) + 3 * k from by ring]
    step fm; step fm; step fm
    exact ih (D + 1) (E + 3)

private theorem outer_step (B C D E : ℕ) :
    ⟨(0 : ℕ), B + 4, C + 1, D + 1, E⟩ [fm]⊢* ⟨0, B, C + 2, D, E + 1⟩ := by
  step fm; step fm; step fm; ring_nf; finish

private theorem outer_loop : ∀ k, ∀ C D E,
    ⟨(0 : ℕ), 4 * k + 3, C + 1, D + k, E⟩ [fm]⊢* ⟨0, 3, C + 1 + k, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro C D E
  · ring_nf; finish
  · rw [show 4 * (k + 1) + 3 = (4 * k + 3) + 4 from by ring,
        show D + (k + 1) = (D + k) + 1 from by ring]
    apply stepStar_trans (outer_step (4 * k + 3) C (D + k) E)
    rw [show C + 2 = (C + 1) + 1 from by ring,
        show C + 1 + (k + 1) = (C + 1) + 1 + k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    exact ih (C + 1) D (E + 1)

private theorem partial_round (C D E : ℕ) :
    ⟨(0 : ℕ), 3, C + 1, D + 1, E⟩ [fm]⊢* ⟨0, 1, C + 1, D + 1, E + 2⟩ := by
  step fm; step fm; step fm; ring_nf; finish

private theorem phase2345 (n : ℕ) :
    ⟨(0 : ℕ), 4 * n + 1, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨0, 1, 0, n + 2, 4 * n + 4⟩ := by
  rcases n with _ | n
  · execute fm 5
  · -- n+1 >= 1
    -- State: (0, 4*(n+1)+1, 0, (n+1)+1, 0) = (0, 4n+5, 0, n+2, 0)
    rw [show 4 * (n + 1) + 1 = (4 * n + 3) + 2 from by ring]
    -- R4 step: need d+1 pattern. (n+1)+1 = n+2 and we need d+1 form.
    apply step_stepStar_stepPlus
    · show fm ⟨0, (4 * n + 3) + 2, 0, (n + 1) + 1, 0⟩ = some ⟨1, (4 * n + 3) + 2, 1, n + 1, 0⟩
      unfold fm; simp only
    -- R0 step
    step fm
    -- State: (0, 4*n+3, 2, n+1, 0)
    -- outer_loop n 1 1 0 expects (0, 4*n+3, 1+1, 1+n, 0)
    -- Need 2 = 1+1 and n+1 = 1+n
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show n + 1 = 1 + n from by ring]
    apply stepStar_trans (outer_loop n 1 1 0)
    -- State: (0, 3, 1+1+n, 1, 0+n)
    -- = (0, 3, n+2, 1, n)
    -- partial_round (n+1) 0 n expects (0, 3, (n+1)+1, 0+1, n)
    -- 1+1+n = (n+1)+1 by ring
    -- 1 = 0+1
    rw [show 1 + 1 + n = (1 + n) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring,
        show (0 : ℕ) + n = n from by ring]
    apply stepStar_trans (partial_round (1 + n) 0 n)
    -- State: (0, 1, (1+n)+1, 0+1, n+2)
    -- = (0, 1, n+2, 1, n+2)
    -- inner_loop (n+2) 0 (n+2) expects (0, 1, n+2, 0+1, n+2)
    rw [show (0 : ℕ) + 1 = 1 from by ring,
        show (1 + n) + 1 = n + 2 from by ring]
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (inner_loop (n + 2) 0 (n + 2))
    -- State: (0, 1, 0, 0+1+(n+2), (n+2)+3*(n+2))
    -- = (0, 1, 0, n+3, 4n+8)
    -- Target: (0, 1, 0, (1+n)+1+1, 4*(1+n)+4)
    -- = (0, 1, 0, n+3, 4n+8)
    -- Need definitional or ring equality
    rw [show 0 + 1 + (n + 2) = (1 + n) + 1 + 1 from by ring,
        show (n + 2) + 3 * (n + 2) = 4 * (1 + n) + 4 from by ring]
    finish

private theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 1, 0, n + 1, 4 * n⟩ [fm]⊢⁺ ⟨0, 1, 0, n + 2, 4 * n + 4⟩ := by
  rcases n with _ | n
  · execute fm 5
  · apply stepStar_stepPlus_stepPlus
    · exact r3_drain (4 * (n + 1)) 1 (n + 2)
    rw [show 1 + 4 * (n + 1) = 4 * (n + 1) + 1 from by ring]
    exact phase2345 (n + 1)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 1, 0, n + 1, 4 * n⟩) 0
  intro n; exists n + 1; exact main_trans n

end Sz22_2003_unofficial_1061
