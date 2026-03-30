import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #925: [4/15, 33/14, 25/2, 49/11, 21/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  2 -1
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_925

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Phase: R2+R1 interleaved chain (k rounds)
theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    have := ih (a + 1) c d (e + 1)
    ring_nf at this ⊢; exact this

-- Phase: R3 drain (j steps, a -> c)
theorem r3_drain : ∀ j, ∀ c e,
    ⟨j, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * j, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro c e
  · exists 0
  · step fm
    have := ih (c + 2) e
    ring_nf at this ⊢; exact this

-- Phase: R4 drain (k steps, e -> d)
theorem e_to_d : ∀ k, ∀ c d e,
    ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    have := ih c (d + 2) e
    ring_nf at this ⊢; exact this

-- Main transition: (0, 0, c + d + 3, d, 0) ⊢⁺ (0, 0, c + 2*d + 6, 2*d + 2, 0)
theorem main_trans (c d : ℕ) :
    ⟨0, 0, c + d + 3, d, 0⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * d + 6, 2 * d + 2, 0⟩ := by
  -- R5: (0, 0, c+d+3, d, 0) -> (0, 1, c+d+2, d+1, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, c + d + 3, d, 0⟩ = some ⟨0, 1, c + d + 2, d + 1, 0⟩
    unfold fm; simp only
  -- R1: (0, 1, c+d+2, d+1, 0) -> (2, 0, c+d+1, d+1, 0)
  have h0 : ⟨0, 1, c + d + 2, d + 1, 0⟩ [fm]⊢* ⟨2, 0, c + d + 1, d + 1, 0⟩ := by
    step fm; ring_nf; finish
  -- R2+R1 chain (d+1 rounds)
  have h1 : ⟨2, 0, c + d + 1, d + 1, 0⟩ [fm]⊢*
      ⟨d + 3, 0, c, 0, d + 1⟩ := by
    have := r2r1_chain (d + 1) 1 c 0 0
    ring_nf at this ⊢; exact this
  -- R3 drain (d+3 steps)
  have h2 : ⟨d + 3, 0, c, 0, d + 1⟩ [fm]⊢*
      ⟨0, 0, c + 2 * d + 6, 0, d + 1⟩ := by
    have := r3_drain (d + 3) c (d + 1)
    ring_nf at this ⊢; exact this
  -- R4 drain (d+1 steps)
  have h3 : ⟨0, 0, c + 2 * d + 6, 0, d + 1⟩ [fm]⊢*
      ⟨0, 0, c + 2 * d + 6, 2 * d + 2, 0⟩ := by
    have := e_to_d (d + 1) (c + 2 * d + 6) 0 0
    ring_nf at this ⊢; exact this
  exact stepStar_trans h0 (stepStar_trans h1 (stepStar_trans h2 h3))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 2, 0⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, p.1 + p.2 + 3, p.2, 0⟩) ⟨0, 2⟩
  intro ⟨c, d⟩
  refine ⟨⟨c + 1, 2 * d + 2⟩, ?_⟩
  show ⟨0, 0, c + d + 3, d, 0⟩ [fm]⊢⁺
    ⟨0, 0, (c + 1) + (2 * d + 2) + 3, 2 * d + 2, 0⟩
  rw [show (c + 1) + (2 * d + 2) + 3 = c + 2 * d + 6 from by ring]
  exact main_trans c d

end Sz22_2003_unofficial_925
