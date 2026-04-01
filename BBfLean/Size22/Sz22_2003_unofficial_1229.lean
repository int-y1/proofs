import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1229: [5/6, 5929/2, 4/35, 3/11, 22/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  2
 2  0 -1 -1  0
 0  1  0  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1229

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R4 repeated: move e to b
theorem e_to_b : ∀ k b d, ⟨(0 : ℕ), b, 0, d, 0 + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro b d; exists 0
  · intro b d
    rw [Nat.add_succ 0 k]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- R3,R1,R1 chain with e carried along: k rounds
theorem r3r1r1_chain : ∀ k b c d e, ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k + 1, d, e⟩ := by
  intro k; induction' k with k ih
  · intro b c d e; exists 0
  · intro b c d e
    rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    rw [show c + k + 1 = (c + k) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm
    step fm
    step fm
    rw [show c + k + 2 = c + (k + 1) + 1 from by ring]
    finish

-- R3,R2,R2 chain: k rounds, each c-=1, d+=3, e+=4
theorem r3r2r2_chain : ∀ k c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + 3 * k + 1, e + 4 * k⟩ := by
  intro k; induction' k with k ih
  · intro c d e; simp; exists 0
  · intro c d e
    rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e)
    step fm
    step fm
    step fm
    rw [show d + 3 * k + 1 + 3 = d + 3 * (k + 1) + 1 from by ring,
        show e + 4 * k + 4 = e + 4 * (k + 1) from by ring]
    finish

-- Main transition: (0,0,0, m+k+2, 2m+1) ->+ (0,0,0, 3m+k+4, 4m+5)
theorem main_trans (m k : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, m + k + 2, 2 * m + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 3 * m + k + 4, 4 * m + 5⟩ := by
  -- Phase 1: R4 x (2m+1): move e to b
  rw [show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m + 1) 0 (m + k + 2))
  rw [show (0 : ℕ) + (2 * m + 1) = 2 * m + 1 from by ring]
  -- State: (0, 2m+1, 0, m+k+2, 0)
  -- Phase 2: R5
  rw [show m + k + 2 = (m + k + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 2 * m + 1, 0, (m + k + 1) + 1, 0⟩ : Q) [fm]⊢
      ⟨1, 2 * m + 1, 0, m + k + 1, 1⟩)
  -- Phase 3: R1
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  apply stepStar_trans
    (step_stepStar (by simp [fm] : (⟨1, (2 * m) + 1, 0, m + k + 1, 1⟩ : Q) [fm]⊢
      ⟨0, 2 * m, 1, m + k + 1, 1⟩))
  -- State: (0, 2m, 1, m+k+1, 1)
  -- Phase 4: R3,R1,R1 x m rounds
  rw [show 2 * m = 0 + 2 * m from by ring,
      show m + k + 1 = (k + 1) + m from by ring]
  apply stepStar_trans (r3r1r1_chain m 0 0 (k + 1) 1)
  rw [show 0 + m + 1 = m + 1 from by ring]
  -- State: (0, 0, m+1, k+1, 1)
  -- Phase 5: R3,R2,R2 x (m+1) rounds
  rw [show m + 1 = 0 + (m + 1) from by ring,
      show (k + 1 : ℕ) = k + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (m + 1) 0 k 1)
  rw [show k + 3 * (m + 1) + 1 = 3 * m + k + 4 from by ring,
      show 1 + 4 * (m + 1) = 4 * m + 5 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 7⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, k⟩ ↦ ⟨0, 0, 0, m + k + 2, 2 * m + 1⟩) ⟨3, 0⟩
  intro ⟨m, k⟩
  exists ⟨2 * m + 2, m + k⟩
  show ⟨(0 : ℕ), (0 : ℕ), 0, m + k + 2, 2 * m + 1⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), 0, (2 * m + 2) + (m + k) + 2, 2 * (2 * m + 2) + 1⟩
  rw [show (2 * m + 2) + (m + k) + 2 = 3 * m + k + 4 from by ring,
      show 2 * (2 * m + 2) + 1 = 4 * m + 5 from by ring]
  exact main_trans m k

end Sz22_2003_unofficial_1229
