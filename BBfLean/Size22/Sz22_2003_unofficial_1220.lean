import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1220: [5/6, 539/2, 484/35, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  2
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1220

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move e to b
theorem e_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih
  · intro b d e; exists 0
  · intro b d e
    rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R3+R1+R1 chain: k rounds, each consuming 2 from b, 1 from d, producing 1 c and 2 e
theorem r3r1r1_chain : ∀ k, ∀ b c d e, ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k + 1, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    rw [show c + k + 1 = (c + k) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm
    step fm
    step fm
    rw [show c + k + 2 = c + (k + 1) + 1 from by ring,
        show e + 2 * k + 2 = e + 2 * (k + 1) from by ring]
    finish

-- R3+R2+R2 chain: k rounds, each consuming 1 from c, adding 3 to d, adding 4 to e
theorem r3r2r2_chain : ∀ k c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + 3 * k + 1, e + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e)
    step fm
    step fm
    step fm
    rw [show d + 3 * k + 1 + 3 = d + 3 * (k + 1) + 1 from by ring,
        show e + 4 * k + 4 = e + 4 * (k + 1) from by ring]
    finish

-- Main transition: (0, 0, 0, n+2, 2*n+1) ->+ (0, 0, 0, 3*n+5, 6*n+7)
theorem main_transition (n : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, n + 2, 2 * n + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 3 * n + 5, 6 * n + 7⟩ := by
  -- Phase 1: move e to b
  rw [show 2 * n + 1 = 0 + (2 * n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * n + 1) 0 (n + 2) 0)
  rw [show (0 : ℕ) + (2 * n + 1) = 2 * n + 1 from by ring]
  -- State: (0, 2n+1, 0, n+2, 0)
  -- Phase 2: R5
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (by simp [fm] : (⟨0, 2 * n + 1, 0, (n + 1) + 1, 0⟩ : Q) [fm]⊢ ⟨0, 2 * n + 1, 1, n + 1, 0⟩)
  -- State: (0, 2n+1, 1, n+1, 0)
  -- Phase 3: R3+R1+R1 chain, n rounds
  rw [show 2 * n + 1 = 1 + 2 * n from by ring,
      show n + 1 = 1 + n from by ring]
  apply stepStar_trans (r3r1r1_chain n 1 0 1 0)
  rw [show 0 + n + 1 = n + 1 from by ring]
  -- State: (0, 1, n+1, 1, 2n)
  -- Phase 4: partial round R3+R1+R2
  step fm
  step fm
  step fm
  -- State: (0, 0, n+1, 2, 2n+3)
  rw [show (0 : ℕ) + 2 * n + 2 + 1 = 2 * n + 3 from by omega]
  -- Phase 5: drain R3+R2+R2 chain, n+1 rounds
  rw [show n + 1 = 0 + (n + 1) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (n + 1) 0 1 (2 * n + 3))
  rw [show 1 + 3 * (n + 1) + 1 = 3 * n + 5 from by ring,
      show 2 * n + 3 + 4 * (n + 1) = 6 * n + 7 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, 2 * n + 1⟩) 0
  intro n
  exists n * 3 + 3
  show ⟨(0 : ℕ), (0 : ℕ), 0, n + 2, 2 * n + 1⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), 0, (n * 3 + 3) + 2, 2 * (n * 3 + 3) + 1⟩
  have h := main_transition n
  rw [show 3 * n + 5 = (n * 3 + 3) + 2 from by ring,
      show 6 * n + 7 = 2 * (n * 3 + 3) + 1 from by ring] at h
  exact h

end Sz22_2003_unofficial_1220
