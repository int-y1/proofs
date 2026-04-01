import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1214: [5/6, 539/2, 44/35, 3/11, 25/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  1
 0  1  0  0 -1
 0  0  2 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1214

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

theorem e_to_b : ∀ k b d, ⟨(0 : ℕ), b, 0, d, k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm
    exact ih (b + 1) d

theorem r3r1r1_chain : ∀ k, ∀ b c d e, ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    rw [show c + k + 1 = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show c + k + 2 = c + (k + 1) + 1 from by ring,
        show e + k + 1 = e + (k + 1) from by ring]
    finish

theorem r3r2r2_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + 3 * k + 1, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 3))
    ring_nf; finish

theorem main_transition (e f : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, e + f + 2, 2 * e⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 3 * e + f + 7, 4 * e + 6⟩ := by
  -- Phase 1: R4 chain, move 2*e from e to b
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * e) 0 (e + f + 2))
  -- Goal: (0, 0+2*e, 0, e+f+2, 0) ⊢⁺ ...
  -- Phase 2: R5 step
  rw [show e + f + 2 = (e + f + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0 + 2 * e, 0, (e + f + 1) + 1, 0⟩ : Q) [fm]⊢ ⟨0, 0 + 2 * e, 2, e + f + 1, 0⟩)
  -- Phase 3: R3+R1+R1 chain (e rounds)
  rw [show e + f + 1 = (f + 1) + e from by ring]
  apply stepStar_trans (r3r1r1_chain e 0 1 (f + 1) 0)
  rw [show 1 + e + 1 = e + 2 from by ring,
      show (0 : ℕ) + e = e from by ring]
  -- Phase 4: R3+R2+R2 chain (e+2 rounds)
  rw [show e + 2 = 0 + (e + 2) from by ring,
      show f + 1 = f + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (e + 2) 0 f e)
  rw [show f + 3 * (e + 2) + 1 = 3 * e + f + 7 from by ring,
      show e + 3 * (e + 2) = 4 * e + 6 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 8, 8⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨e, f⟩ ↦ ⟨0, 0, 0, e + f + 2, 2 * e⟩) ⟨4, 2⟩
  intro ⟨e, f⟩
  refine ⟨⟨2 * e + 3, e + f + 2⟩, ?_⟩
  show ⟨(0 : ℕ), (0 : ℕ), 0, e + f + 2, 2 * e⟩ [fm]⊢⁺
    ⟨0, 0, 0, (2 * e + 3) + (e + f + 2) + 2, 2 * (2 * e + 3)⟩
  rw [show (2 * e + 3) + (e + f + 2) + 2 = 3 * e + f + 7 from by ring,
      show 2 * (2 * e + 3) = 4 * e + 6 from by ring]
  exact main_transition e f

end Sz22_2003_unofficial_1214
