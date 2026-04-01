import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1332: [63/10, 2/33, 1331/2, 5/7, 10/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  3
 0  0  1 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1332

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R1+R2 interleaved chain: consume c register via alternating R1 and R2
-- From (1, b, k+1, d, e+k) to (0, b+k+2, 0, d+k+1, e)
theorem r1r2_chain : ∀ k, ∀ b d e,
    ⟨(1 : ℕ), b, k + 1, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k + 2, (0 : ℕ), d + k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · step fm; finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show (k : ℕ) + 1 + 1 = (k + 1) + 1 from by ring]
    step fm  -- R1: (0, b+2, k+1, d+1, e+k+1)
    step fm  -- R2: (1, b+1, k+1, d+1, e+k)
    apply stepStar_trans (ih (b + 1) (d + 1) e)
    ring_nf; finish

-- R2 chain: drain b and e together
theorem r2_chain : ∀ k, ∀ a d e,
    ⟨a, k, (0 : ℕ), d, e + k⟩ [fm]⊢* ⟨a + k, (0 : ℕ), (0 : ℕ), d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R2: (a+1, k, 0, d, e+k)
    apply stepStar_trans (ih (a + 1) d e)
    ring_nf; finish

-- R3 chain: drain a, adding 3 to e per step
theorem r3_chain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), (0 : ℕ), d, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm  -- R3: (k, 0, 0, d, e+3)
    apply stepStar_trans (ih d (e + 3))
    ring_nf; finish

-- R4 chain: transfer d to c
theorem r4_chain : ∀ k, ∀ c e,
    ⟨(0 : ℕ), (0 : ℕ), c, k, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + k, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm  -- R4: (0, 0, c+1, k, e)
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

-- Main transition: (0, 0, c, 0, f + 2*c + 3) →⁺ (0, 0, c+1, 0, (f+c+1) + 2*(c+1) + 3)
theorem main_trans (c f : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), c, (0 : ℕ), f + 2 * c + 3⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), c + 1, (0 : ℕ), f + 3 * c + 6⟩ := by
  -- Phase 1: R5 (1 step)
  rw [show f + 2 * c + 3 = (f + 2 * c + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0, c, 0, (f + 2 * c + 2) + 1⟩ : Q) [fm]⊢
      ⟨1, 0, c + 1, 0, f + 2 * c + 2⟩)
  -- State: (1, 0, c+1, 0, f+2c+2)
  -- Phase 2: R1+R2 interleaved (c+1 R1, c R2)
  rw [show f + 2 * c + 2 = (f + c + 2) + c from by ring]
  apply stepStar_trans (r1r2_chain c 0 0 (f + c + 2))
  rw [show (0 : ℕ) + c + 2 = c + 2 from by ring,
      show (0 : ℕ) + c + 1 = c + 1 from by ring]
  -- State: (0, c+2, 0, c+1, f+c+2)
  -- Phase 3: R2 drain (c+2 steps)
  rw [show f + c + 2 = f + (c + 2) from by ring]
  apply stepStar_trans (r2_chain (c + 2) 0 (c + 1) f)
  rw [show (0 : ℕ) + (c + 2) = c + 2 from by ring]
  -- State: (c+2, 0, 0, c+1, f)
  -- Phase 4: R3 drain (c+2 steps)
  apply stepStar_trans (r3_chain (c + 2) (c + 1) f)
  -- State: (0, 0, 0, c+1, f+3*(c+2))
  -- Phase 5: R4 drain (c+1 steps)
  rw [show f + 3 * (c + 2) = f + 3 * c + 6 from by ring]
  apply stepStar_trans (r4_chain (c + 1) 0 (f + 3 * c + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 3⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, f⟩ ↦ ⟨0, 0, c, 0, f + 2 * c + 3⟩) ⟨0, 0⟩
  intro ⟨c, f⟩
  refine ⟨⟨c + 1, f + c + 1⟩, ?_⟩
  show ⟨(0 : ℕ), (0 : ℕ), c, (0 : ℕ), f + 2 * c + 3⟩ [fm]⊢⁺
       ⟨(0 : ℕ), (0 : ℕ), c + 1, (0 : ℕ), (f + c + 1) + 2 * (c + 1) + 3⟩
  rw [show (f + c + 1) + 2 * (c + 1) + 3 = f + 3 * c + 6 from by ring]
  exact main_trans c f

end Sz22_2003_unofficial_1332
