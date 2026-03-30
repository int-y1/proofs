import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #847: [36/35, 5/22, 49/2, 11/3, 25/7]

Vector representation:
```
 2  2 -1 -1  0
-1  0  1  0 -1
-1  0  0  2  0
 0 -1  0  0  1
 0  0  2 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_847

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

-- R2-R1 interleaving: each round applies R2 then R1.
-- Net per round: a+1, b+2, d-1, e-1, c stays 0.
theorem r2r1_chain : ∀ k a b d e, ⟨a + 1, b, 0, d + k, e + k⟩ [fm]⊢* ⟨a + k + 1, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 2) d e)
    ring_nf; finish

-- R3 chain: convert a to d.
theorem r3_chain : ∀ k a b d, ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (d + 2))
    ring_nf; finish

-- R4 chain: convert b to e.
theorem r4_chain : ∀ k b d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, e+g+3, e) →⁺ (0, 0, 0, 2*e+g+8, 2*e+4)
theorem main_trans : ∀ g e, ⟨0, 0, 0, e + g + 3, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * e + g + 8, 2 * e + 4⟩ := by
  intro g e
  -- Phase 1: R5
  rw [show e + g + 3 = (e + g + 2) + 1 from by ring]
  step fm
  -- Phase 1: R1 (c=2, d=e+g+1+1)
  rw [show e + g + 2 = (e + g + 1) + 1 from by ring]
  step fm
  -- Phase 1: R1 (c=1, d=e+g+1)
  rw [show e + g + 1 = (e + g) + 1 from by ring]
  step fm
  -- Now at (4, 4, 0, e+g, e). Need to match r2r1_chain signature.
  -- r2r1_chain e 3 4 g 0 : (3+1, 4, 0, g+e, 0+e) →* (3+e+1, 4+2*e, 0, g, 0)
  -- Use conv or explicit rewriting
  have phase2 := r2r1_chain e 3 4 g 0
  rw [show 0 + e = e from by ring, show g + e = e + g from by ring] at phase2
  apply stepStar_trans phase2
  -- Now at (3+e+1, 4+2*e, 0, g, 0) = (e+4, 2*e+4, 0, g, 0)
  have phase3 := r3_chain (3 + e + 1) 0 (4 + 2 * e) g
  rw [show 0 + (3 + e + 1) = 3 + e + 1 from by ring] at phase3
  apply stepStar_trans phase3
  -- Now at (0, 4+2*e, 0, g+2*(3+e+1), 0)
  have phase4 := r4_chain (4 + 2 * e) 0 (g + 2 * (3 + e + 1)) 0
  rw [show 0 + (4 + 2 * e) = 4 + 2 * e from by ring] at phase4
  apply stepStar_trans phase4
  rw [show 4 + 2 * e = 2 * e + 4 from by ring,
      show g + 2 * (3 + e + 1) = 2 * e + g + 8 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 7, 4⟩)
  · execute fm 12
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ e + 3)
  · intro c ⟨d, e, hq, hd⟩; subst hq
    obtain ⟨g, rfl⟩ : ∃ g, d = e + g + 3 := ⟨d - e - 3, by omega⟩
    exact ⟨⟨0, 0, 0, 2 * e + g + 8, 2 * e + 4⟩,
      ⟨2 * e + g + 8, 2 * e + 4, rfl, by omega⟩,
      main_trans g e⟩
  · exact ⟨7, 4, rfl, by omega⟩

end Sz22_2003_unofficial_847
