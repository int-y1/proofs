import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #503: [28/15, 3/22, 325/2, 121/7, 3/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  2  0  0  1
 0  0  0 -1  2  0
 0  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_503

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+2, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- R4 repeated: d to e
theorem d_to_e : ∀ k c d e f, ⟨0, 0, c, d + k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e + 2 * k, f⟩ := by
  intro k; induction' k with k h <;> intro c d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by omega]
  step fm
  apply stepStar_trans (h c d (e + 2) f)
  ring_nf; finish

-- R2+R1 chain. Note: a+2 = (a+1)+1 matches R2 pattern (a+1, ...)
-- Each round: R2 then R1, consuming 1 from c and e, adding 1 to a and d
theorem r2r1_chain : ∀ k a c d e f, ⟨a + 2, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 + k, 0, c, d + k, e, f⟩ := by
  intro k; induction' k with k h <;> intro a c d e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by omega,
      show e + (k + 1) = (e + k) + 1 from by omega]
  step fm; step fm
  apply stepStar_trans (h _ _ _ _ _)
  ring_nf; finish

-- R3 repeated: a to c and f
theorem r3_chain : ∀ k a c d f, ⟨a + k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d, 0, f + k⟩ := by
  intro k; induction' k with k h <;> intro a c d f
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by omega]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Main transition
theorem main_trans (d c f : ℕ) :
    ⟨0, 0, c + 2 * d + 1, d, 0, f + 1⟩ [fm]⊢⁺ ⟨0, 0, c + 4 * d + 4, 2 * d + 1, 0, f + 2 * d + 2⟩ := by
  -- Phase 1: R4 × d
  have p1 : ⟨0, 0, c + 2 * d + 1, d, 0, f + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * d + 1, 0, 2 * d, f + 1⟩ := by
    have h := d_to_e d (c + 2 * d + 1) 0 0 (f + 1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2+3: R5 then R1
  have p23 : ⟨0, 0, c + 2 * d + 1, 0, 2 * d, f + 1⟩ [fm]⊢⁺ ⟨2, 0, c + 2 * d, 1, 2 * d, f⟩ := by
    rw [show c + 2 * d + 1 = (c + 2 * d) + 1 from by omega]
    step fm; step fm; finish
  -- Phase 4: R2+R1 × (2d)
  have p4 : ⟨2, 0, c + 2 * d, 1, 2 * d, f⟩ [fm]⊢* ⟨2 + 2 * d, 0, c, 1 + 2 * d, 0, f⟩ := by
    have h := r2r1_chain (2 * d) 0 c 1 0 f
    simp only [Nat.zero_add] at h; exact h
  -- Phase 5: R3 × (2+2d)
  have p5 : ⟨2 + 2 * d, 0, c, 1 + 2 * d, 0, f⟩ [fm]⊢*
      ⟨0, 0, c + 2 * (2 + 2 * d), 1 + 2 * d, 0, f + (2 + 2 * d)⟩ := by
    have h := r3_chain (2 + 2 * d) 0 c (1 + 2 * d) f
    simp only [Nat.zero_add] at h; exact h
  -- Rewrite p5 target to match final goal
  have p5' : ⟨2 + 2 * d, 0, c, 1 + 2 * d, 0, f⟩ [fm]⊢*
      ⟨0, 0, c + 4 * d + 4, 2 * d + 1, 0, f + 2 * d + 2⟩ := by
    rw [show (2 * d + 1 : ℕ) = 1 + 2 * d from by omega,
        show (c + 4 * d + 4 : ℕ) = c + 2 * (2 + 2 * d) from by ring,
        show (f + 2 * d + 2 : ℕ) = f + (2 + 2 * d) from by omega]
    exact p5
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus (stepPlus_stepStar_stepPlus p23 p4) p5')

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨c, d, f⟩ ↦ ⟨0, 0, c + 2 * d + 1, d, 0, f + 1⟩) ⟨1, 0, 0⟩
  intro ⟨c, d, f⟩
  refine ⟨⟨c + 1, 2 * d + 1, f + 2 * d + 1⟩, ?_⟩
  simp only []
  rw [show (c + 1) + 2 * (2 * d + 1) + 1 = c + 4 * d + 4 from by ring,
      show (f + 2 * d + 1) + 1 = f + 2 * d + 2 from by omega]
  exact main_trans d c f
