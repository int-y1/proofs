import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1188: [5/6, 49/2, 484/35, 3/11, 10/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  2
 0  1  0  0 -1
 1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1188

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 chain: (0, b, 0, d, k) →* (0, b+k, 0, d, 0).
theorem e_to_b : ∀ k b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- Interleave chain: (1, 2*k, c, d+k, e) →* (1, 0, c+k, d, e+2*k).
theorem interleave_chain : ∀ k c d e, ⟨1, 2 * k, c, d + k, e⟩ [fm]⊢* ⟨1, 0, c + k, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show d + k + 1 = (d + k) + 1 from by ring]
    step fm
    rw [show (2 * k + 1) + 1 = 2 * k + 1 + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d (e + 2))
    ring_nf; finish

-- R3+R2+R2 chain: (0, 0, c+k, d+k, e) →* (0, 0, c, d+4*k, e+2*k).
theorem r3r2r2_chain : ∀ k c d e, ⟨0, 0, c + k, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d + 4 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + k + 2 + 2 = (d + 4) + k from by ring]
    apply stepStar_trans (ih c (d + 4) (e + 2))
    ring_nf; finish

-- Main transition: (0,0,0,D+2*f+2,2*f) →⁺ (0,0,0,D+4*f+6,4*f+2).
theorem main_trans (f D : ℕ) :
    ⟨0, 0, 0, D + 2 * f + 2, 2 * f⟩ [fm]⊢⁺ ⟨0, 0, 0, D + 4 * f + 6, 4 * f + 2⟩ := by
  -- Phase 1: R4 drain: →* (0, 2*f, 0, D+2*f+2, 0)
  have phase1 : ⟨0, 0, 0, D + 2 * f + 2, 2 * f⟩ [fm]⊢* ⟨0, 2 * f, 0, D + 2 * f + 2, 0⟩ := by
    have := e_to_b (2 * f) 0 (D + 2 * f + 2)
    simpa using this
  -- Phase 2+3+4: R5 + interleave + R2
  have phase234 : ⟨0, 2 * f, 0, D + 2 * f + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 1 + f, D + f + 3, 2 * f⟩ := by
    rw [show D + 2 * f + 2 = (D + 2 * f + 1) + 1 from by ring]
    step fm
    rw [show D + 2 * f + 1 = (D + f + 1) + f from by ring]
    apply stepStar_trans (interleave_chain f 1 (D + f + 1) 0)
    rw [show 0 + 2 * f = 2 * f from by ring]
    step fm
    rw [show D + f + 1 + 2 = D + f + 3 from by ring]
    finish
  -- Phase 5: R3+R2+R2 chain
  have phase5 : ⟨0, 0, 1 + f, D + f + 3, 2 * f⟩ [fm]⊢* ⟨0, 0, 0, D + 4 * f + 6, 4 * f + 2⟩ := by
    rw [show (1 : ℕ) + f = 0 + (f + 1) from by ring,
        show D + f + 3 = (D + 2) + (f + 1) from by ring]
    apply stepStar_trans (r3r2r2_chain (f + 1) 0 (D + 2) (2 * f))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus phase1 (stepPlus_stepStar_stepPlus phase234 phase5)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D f, q = ⟨0, 0, 0, D + 2 * f + 2, 2 * f⟩)
  · intro c ⟨D, f, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, D + 4 * f + 6, 4 * f + 2⟩,
      ⟨D + 2, 2 * f + 1, by ring_nf⟩,
      main_trans f D⟩
  · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_1188
