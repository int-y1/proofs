import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1272: [5/6, 99/35, 8/5, 7/11, 55/2]

Vector representation:
```
-1 -1  1  0  0
 0  2 -1 -1  1
 3  0 -1  0  0
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1272

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R2+R1+R1 chain: k rounds draining d, building c and e
theorem r2r1r1_chain : ∀ k, ∀ a c e,
    ⟨a + 2 * k, (0 : ℕ), c + 1, k, e⟩ [fm]⊢*
    ⟨a, (0 : ℕ), c + k + 1, (0 : ℕ), e + k⟩ := by
  intro k; induction' k with k ih
  · intro a c e; simp; exists 0
  · intro a c e
    rw [show a + 2 * (k + 1) = (a + 2 * k + 1) + 1 from by ring,
        show (k + 1) = k + 1 from rfl]
    step fm
    rw [show a + 2 * k + 1 = (a + 2 * k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1))
    rw [show c + 1 + k + 1 = c + (k + 1) + 1 from by ring,
        show e + 1 + k = e + (k + 1) from by ring]
    finish

-- R3 chain: drain c, add 3 to a per round
theorem r3_chain : ∀ k, ∀ a e,
    ⟨a, (0 : ℕ), k, (0 : ℕ), e⟩ [fm]⊢*
    ⟨a + 3 * k, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih
  · intro a e; simp; exists 0
  · intro a e
    rw [show (k + 1) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 3) e)
    rw [show a + 3 + 3 * k = a + 3 * (k + 1) from by ring]
    finish

-- R4 chain: move e to d
theorem r4_chain : ∀ k, ∀ a d,
    ⟨a, (0 : ℕ), (0 : ℕ), d, k⟩ [fm]⊢*
    ⟨a, (0 : ℕ), (0 : ℕ), d + k, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih
  · intro a d; simp; exists 0
  · intro a d
    rw [show (k + 1) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (d + 1))
    rw [show d + 1 + k = d + (k + 1) from by ring]
    finish

-- Main transition: (a + 2*d + 1, 0, 0, d, 0) ->+ (a + 3*d + 3, 0, 0, d+1, 0)
theorem main_transition (a d : ℕ) :
    ⟨a + 2 * d + 1, (0 : ℕ), (0 : ℕ), d, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨a + 3 * d + 3, (0 : ℕ), (0 : ℕ), d + 1, (0 : ℕ)⟩ := by
  -- R5: (a+2d+1, 0, 0, d, 0) -> (a+2d, 0, 1, d, 1)
  rw [show a + 2 * d + 1 = (a + 2 * d) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨(a + 2 * d) + 1, 0, 0, d, 0⟩ : Q) [fm]⊢ ⟨a + 2 * d, 0, 1, d, 1⟩)
  -- Apply R2+R1+R1 chain with k=d
  apply stepStar_trans (r2r1r1_chain d a 0 1)
  -- State: (a, 0, d+1, 0, d+1)
  rw [show 0 + d + 1 = d + 1 from by ring,
      show 1 + d = d + 1 from by ring]
  -- Apply R3 chain with k=d+1
  apply stepStar_trans (r3_chain (d + 1) a (d + 1))
  -- State: (a + 3*(d+1), 0, 0, 0, d+1)
  -- Apply R4 chain with k=d+1
  apply stepStar_trans (r4_chain (d + 1) (a + 3 * (d + 1)) 0)
  rw [show (0 : ℕ) + (d + 1) = d + 1 from by ring,
      show a + 3 * (d + 1) = a + 3 * d + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨6, 0, 0, 2, 0⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 2 * d + 1, 0, 0, d, 0⟩) ⟨1, 2⟩
  intro ⟨a, d⟩
  exists ⟨a + d, d + 1⟩
  show ⟨a + 2 * d + 1, (0 : ℕ), (0 : ℕ), d, (0 : ℕ)⟩ [fm]⊢⁺
       ⟨(a + d) + 2 * (d + 1) + 1, (0 : ℕ), (0 : ℕ), d + 1, (0 : ℕ)⟩
  rw [show (a + d) + 2 * (d + 1) + 1 = a + 3 * d + 3 from by ring]
  exact main_transition a d

end Sz22_2003_unofficial_1272
