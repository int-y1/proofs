import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1393: [63/10, 9317/2, 2/33, 5/7, 2/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  1  3
 1 -1  0  0 -1
 0  0  1 -1  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1393

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+3⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 repeated: move d to c.
theorem d_to_c : ∀ k c d e, ⟨(0 : ℕ), (0 : ℕ), c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + k, d, e⟩ := by
  intro k; induction' k with k ih
  · intro c d e; exists 0
  · intro c d e
    rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R1R3 spiral: each round R1 then R3.
theorem r1r3_spiral : ∀ k b c d e, ⟨(1 : ℕ), b, c + k, d, e + k⟩ [fm]⊢* ⟨(1 : ℕ), b + k, c, d + k, e⟩ := by
  intro k; induction' k with k ih
  · intro b c d e; exists 0
  · intro b c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R1
    step fm  -- R3
    apply stepStar_trans (ih (b + 1) c (d + 1) e)
    ring_nf; finish

-- R2R3 drain: each round R2 then R3.
theorem r2r3_drain : ∀ k b d e, ⟨(1 : ℕ), b + k, 0, d, e + 1⟩ [fm]⊢* ⟨(1 : ℕ), b, 0, d + k, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih
  · intro b d e; simp; exists 0
  · intro b d e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + 1 = (e + 1) from rfl]
    step fm  -- R2
    rw [show e + 1 + 3 = (e + 3) + 1 from by ring,
        show b + k + 1 = (b + k) + 1 from by ring]
    step fm  -- R3
    rw [show e + 3 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih b (d + 1) (e + 2))
    ring_nf; finish

-- Main transition: (1, 0, 0, d+2, e+d+3) →⁺ (1, 0, 0, 2*d+6, 2*d+e+8).
theorem main_transition (d e : ℕ) :
    ⟨(1 : ℕ), (0 : ℕ), 0, d + 2, e + d + 3⟩ [fm]⊢⁺
    ⟨(1 : ℕ), (0 : ℕ), 0, 2 * d + 6, 2 * d + e + 8⟩ := by
  -- Phase 1: R2 step
  step fm
  -- State: (0, 0, 0, d+3, e+d+6). Goal is ⊢*.
  rw [show d + 2 + 1 = 0 + (d + 3) from by ring,
      show e + d + 3 + 3 = e + d + 6 from by ring]
  apply stepStar_trans (d_to_c (d + 3) 0 0 (e + d + 6))
  -- State: (0, 0, d+3, 0, e+d+6)
  rw [show e + d + 6 = (e + d + 5) + 1 from by ring,
      show 0 + (d + 3) = (d + 3) from by ring]
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨(0 : ℕ), 0, d + 3, 0, (e + d + 5) + 1⟩ : Q) [fm]⊢ ⟨1, 0, d + 3, 0, e + d + 5⟩))
  -- State: (1, 0, d+3, 0, e+d+5)
  rw [show (d + 3 : ℕ) = 0 + (d + 3) from by ring,
      show e + d + 5 = (e + 2) + (d + 3) from by ring]
  apply stepStar_trans (r1r3_spiral (d + 3) 0 0 0 (e + 2))
  -- State: (1, 0+(d+3), 0, 0+(d+3), e+2)
  rw [show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (r2r3_drain (d + 3) 0 (0 + (d + 3)) (e + 1))
  -- State: (1, 0, 0, 2*d+6, e+1+2*(d+3)+1)
  rw [show 0 + (d + 3) + (d + 3) = 2 * d + 6 from by ring,
      show e + 1 + 2 * (d + 3) + 1 = 2 * d + e + 8 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 3⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨1, 0, 0, d + 2, e + d + 3⟩) ⟨0, 0⟩
  intro ⟨d, e⟩
  exists ⟨2 * d + 4, e + 1⟩
  show ⟨(1 : ℕ), (0 : ℕ), 0, d + 2, e + d + 3⟩ [fm]⊢⁺
       ⟨(1 : ℕ), (0 : ℕ), 0, (2 * d + 4) + 2, (e + 1) + (2 * d + 4) + 3⟩
  rw [show (2 * d + 4) + 2 = 2 * d + 6 from by ring,
      show (e + 1) + (2 * d + 4) + 3 = 2 * d + e + 8 from by ring]
  exact main_transition d e

end Sz22_2003_unofficial_1393
