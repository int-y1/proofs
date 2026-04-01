import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1224: [5/6, 539/2, 676/35, 3/13, 5/11]

Vector representation:
```
-1 -1  1  0  0  0
-1  0  0  2  1  0
 2  0 -1 -1  0  2
 0  1  0  0  0 -1
 0  0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1224

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+2, e+1, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f+2⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R4 repeated: move f to b
theorem f_to_b : ∀ k b d e f, ⟨(0 : ℕ), b, 0, d, e, f + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih
  · intro b d e f; exists 0
  · intro b d e f
    rw [Nat.add_succ f k]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

-- R3/R1/R1 chain: h rounds consuming 2h from b, transferring to c and f
theorem r3r1r1_chain : ∀ k c d e f, ⟨(0 : ℕ), 2 * k, c + 1, d + k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + k + 1, d, e, f + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro c d e f; simp; exists 0
  · intro c d e f
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show c + 1 = c + 1 from rfl,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + k = d + k from rfl,
        show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 1) d e (f + 2))
    ring_nf; finish

-- R3/R2/R2 chain: k rounds
theorem r3r2r2_chain : ∀ k c d e f, ⟨(0 : ℕ), 0, c + k, d + 1, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + 1 + 3 * k, e + 2 * k, f + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro c d e f; simp; exists 0
  · intro c d e f
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm
    step fm
    step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 2) (f + 2))
    ring_nf; finish

-- Main transition
theorem main_trans (d e h : ℕ) :
    ⟨(0 : ℕ), 0, 0, d + h + 2, e + 1, 2 * h⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, d + 3 * h + 5, e + 2 * h + 2, 4 * h + 2⟩ := by
  -- Phase 1: move f to b
  rw [show (2 * h : ℕ) = 0 + 2 * h from by ring]
  apply stepStar_stepPlus_stepPlus (f_to_b (2 * h) 0 (d + h + 2) (e + 1) 0)
  rw [show (0 : ℕ) + 2 * h = 2 * h from by ring]
  -- State: (0, 2*h, 0, d+h+2, e+1, 0)
  -- Phase 2: R5
  rw [show e + 1 = e + 1 from rfl]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 2 * h, 0, d + h + 2, e + 1, 0⟩ : Q) [fm]⊢ ⟨0, 2 * h, 1, d + h + 2, e, 0⟩)
  -- State: (0, 2*h, 1, d+h+2, e, 0)
  -- Phase 3: R3/R1/R1 chain, h rounds
  rw [show d + h + 2 = (d + 2) + h from by ring]
  apply stepStar_trans (r3r1r1_chain h 0 (d + 2) e 0)
  rw [show 0 + h + 1 = h + 1 from by ring,
      show 0 + 2 * h = 2 * h from by ring]
  -- State: (0, 0, h+1, d+2, e, 2*h)
  -- Phase 4: R3/R2/R2 chain, h+1 rounds
  rw [show h + 1 = 0 + (h + 1) from by ring,
      show d + 2 = (d + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (h + 1) 0 (d + 1) e (2 * h))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨d, e, h⟩ ↦ ⟨0, 0, 0, d + h + 2, e + 1, 2 * h⟩) ⟨0, 0, 0⟩
  intro ⟨d, e, h⟩
  exists ⟨d + h + 2, e + 2 * h + 1, 2 * h + 1⟩
  show ⟨(0 : ℕ), 0, 0, d + h + 2, e + 1, 2 * h⟩ [fm]⊢⁺
       ⟨(0 : ℕ), 0, 0, (d + h + 2) + (2 * h + 1) + 2, (e + 2 * h + 1) + 1, 2 * (2 * h + 1)⟩
  rw [show (d + h + 2) + (2 * h + 1) + 2 = d + 3 * h + 5 from by ring,
      show (e + 2 * h + 1) + 1 = e + 2 * h + 2 from by ring,
      show 2 * (2 * h + 1) = 4 * h + 2 from by ring]
  exact main_trans d e h

end Sz22_2003_unofficial_1224
