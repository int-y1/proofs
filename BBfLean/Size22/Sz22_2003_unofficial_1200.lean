import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1200: [5/6, 539/2, 4/35, 1/5, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  0
 0  0 -1  0  0
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1200

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R5 repeated: move e to b
theorem e_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R3+R1+R1 chain: n rounds consuming 2 from b each round
theorem r3r1r1_chain : ∀ k b c d, ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k + 1, d, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih
  · intro b c d; exists 0
  · intro b c d
    rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1))
    rw [show c + k + 1 = (c + k) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm
    step fm
    step fm
    rw [show c + k + 2 = c + (k + 1) + 1 from by ring]
    finish

-- R3+R2+R2 chain: k rounds, each reduces c by 1, adds 3 to d, adds 2 to e
theorem r3r2r2_chain : ∀ k c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + 3 * k + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro c d e; simp; exists 0
  · intro c d e
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e)
    step fm
    step fm
    step fm
    rw [show d + 3 * k + 1 + 3 = d + 3 * (k + 1) + 1 from by ring,
        show e + 2 * k + 2 = e + 2 * (k + 1) from by ring]
    finish

-- Main transition: (0, 0, 0, n^2+2n+2, 2n+1) ->+ (0, 0, 0, (n+1)^2+2(n+1)+2, 2(n+1)+1)
theorem main_transition (n : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, n * n + 2 * n + 2, 2 * n + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, n * n + 4 * n + 5, 2 * n + 3⟩ := by
  -- Phase 1: move e to b
  rw [show 2 * n + 1 = 0 + (2 * n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * n + 1) 0 (n * n + 2 * n + 2) 0)
  rw [show (0 : ℕ) + (2 * n + 1) = 2 * n + 1 from by ring]
  -- State: (0, 2n+1, 0, n^2+2n+2, 0)
  -- R6 step
  rw [show n * n + 2 * n + 2 = (n * n + 2 * n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (by simp [fm] : (⟨0, 2 * n + 1, 0, (n * n + 2 * n + 1) + 1, 0⟩ : Q) [fm]⊢ ⟨0, 2 * n + 1, 1, n * n + 2 * n + 1, 0⟩)
  -- State: (0, 2n+1, 1, n^2+2n+1, 0)
  rw [show 2 * n + 1 = 1 + 2 * n from by ring,
      show n * n + 2 * n + 1 = (n * n + n + 1) + n from by ring]
  apply stepStar_trans (r3r1r1_chain n 1 0 (n * n + n + 1))
  rw [show 0 + n + 1 = n + 1 from by ring]
  -- State: (0, 1, n+1, n^2+n+1, 0)
  -- R3
  rw [show n + 1 = (n) + 1 from by ring,
      show n * n + n + 1 = (n * n + n) + 1 from by ring]
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 1, n + 1, (n * n + n) + 1, 0⟩ : Q) [fm]⊢ ⟨2, 1, n, n * n + n, 0⟩))
  -- R1
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨2, 1, n, n * n + n, 0⟩ : Q) [fm]⊢ ⟨1, 0, n + 1, n * n + n, 0⟩))
  -- R2
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨1, 0, n + 1, n * n + n, 0⟩ : Q) [fm]⊢ ⟨0, 0, n + 1, n * n + n + 2, 1⟩))
  -- State: (0, 0, n+1, n^2+n+2, 1)
  -- Phase 3: n+1 rounds of R3+R2+R2
  rw [show n + 1 = 0 + (n + 1) from by ring,
      show n * n + n + 2 = (n * n + n + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (n + 1) 0 (n * n + n + 1) 1)
  rw [show n * n + n + 1 + 3 * (n + 1) + 1 = n * n + 4 * n + 5 from by ring,
      show 1 + 2 * (n + 1) = 2 * n + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 3⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, (n + 1) * (n + 1) + 2 * (n + 1) + 2, 2 * (n + 1) + 1⟩) 0
  intro n
  exists n + 1
  show ⟨(0 : ℕ), (0 : ℕ), 0, (n + 1) * (n + 1) + 2 * (n + 1) + 2, 2 * (n + 1) + 1⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), 0, (n + 2) * (n + 2) + 2 * (n + 2) + 2, 2 * (n + 2) + 1⟩
  have h := main_transition (n + 1)
  rw [show (n + 1) * (n + 1) + 2 * (n + 1) + 2 = (n + 1) * (n + 1) + 2 * (n + 1) + 2 from rfl] at h
  rw [show (n + 1) * (n + 1) + 4 * (n + 1) + 5 = (n + 2) * (n + 2) + 2 * (n + 2) + 2 from by ring] at h
  rw [show 2 * (n + 1) + 3 = 2 * (n + 2) + 1 from by ring] at h
  exact h

end Sz22_2003_unofficial_1200
