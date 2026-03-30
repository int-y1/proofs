import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #888: [4/15, 147/2, 77/3, 5/539, 3/7]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  2  0
 0 -1  0  1  1
 0  0  1 -2 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_888

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1: R2 chain. Drain a, grow b, add 2 to d per step. c=0 so R1 doesn't fire.
theorem r2_chain : ∀ k, ∀ b d, ⟨a + k, b, 0, d, (0 : ℕ)⟩ [fm]⊢* ⟨a, b + k, 0, d + 2 * k, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) (d + 2))
    ring_nf; finish

-- Phase 2: R3 chain. Drain b when a=0, c=0.
theorem r3_chain : ∀ k, ∀ d e, ⟨(0 : ℕ), k, 0, d, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (d + 1) (e + 1))
    ring_nf; finish

-- Phase 3: R4 chain. a=0, b=0: convert d,e to c.
-- Each step: c += 1, d -= 2, e -= 1.
-- Use decreasing e as the induction variable.
theorem r4_chain : ∀ k, ∀ c, ⟨(0 : ℕ), 0, c, d + 2 * k, k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show d + 2 * (k + 1) = d + 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1))
    ring_nf; finish

-- Phase 4: R2+R1 interleaved chain.
theorem r2r1_chain : ∀ k, ∀ a d, ⟨a + 1, 0, k, d, (0 : ℕ)⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d + 2 * k, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (d + 2))
    ring_nf; finish

-- Spiral: R5 + R1 + R2R1 chain.
theorem spiral : ⟨(0 : ℕ), 0, k + 1, d + 1, (0 : ℕ)⟩ [fm]⊢⁺ ⟨k + 2, 0, 0, d + 2 * k, (0 : ℕ)⟩ := by
  step fm
  step fm
  show ⟨(0 : ℕ) + 1 + 1, 0, k, d, (0 : ℕ)⟩ [fm]⊢* ⟨k + 2, 0, 0, d + 2 * k, (0 : ℕ)⟩
  apply stepStar_trans (r2r1_chain k 1 d)
  ring_nf; finish

-- Phases 1-3 composed.
theorem phases123 : ⟨a + 1, 0, 0, d, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), 0, a + 1, d + a + 1, (0 : ℕ)⟩ := by
  rw [show a + 1 = 0 + (a + 1) from by ring]
  apply stepStar_trans (r2_chain (a + 1) 0 d)
  rw [show (0 : ℕ) + (a + 1) = a + 1 from by ring]
  apply stepStar_trans (r3_chain (a + 1) (d + 2 * (a + 1)) 0)
  rw [show (0 : ℕ) + (a + 1) = a + 1 from by ring,
      show d + 2 * (a + 1) + (a + 1) = d + (a + 1) + 2 * (a + 1) from by ring]
  apply stepStar_trans (r4_chain (a + 1) (d := d + (a + 1)) 0)
  ring_nf; finish

-- Main transition: (a+1, 0, 0, d, 0) ->+ (a+2, 0, 0, d+3*a, 0)
theorem main_trans : ⟨a + 1, 0, 0, d, (0 : ℕ)⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, d + 3 * a, (0 : ℕ)⟩ := by
  apply stepStar_stepPlus_stepPlus phases123
  rw [show d + a + 1 = d + a + 0 + 1 from by ring,
      show a + 1 = a + 0 + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (spiral (k := a + 0) (d := d + a + 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 1, 0, 0, d, (0 : ℕ)⟩) ⟨0, 0⟩
  intro ⟨a, d⟩; exact ⟨⟨a + 1, d + 3 * a⟩, main_trans⟩

end Sz22_2003_unofficial_888
