import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1282: [56/15, 21/22, 5/2, 11/7, 6/5]

Vector representation:
```
 3 -1 -1  1  0
-1  1  0  1 -1
-1  0  1  0  0
 0  0  0 -1  1
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1282

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: drain d to e
theorem d_to_e : ∀ k c d e, ⟨(0 : ℕ), 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c d (e + 1))
    ring_nf; finish

-- R3 repeated: drain a to c
theorem a_to_c : ∀ k a c d, ⟨a + k, (0 : ℕ), c, d, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) d)
    ring_nf; finish

-- R1+R2 chain: E rounds
-- (2k+1, 1, c+E, d+2k, E) ->* (2(k+E)+1, 1, c, d+2(k+E), 0)
theorem r1r2_chain : ∀ E k c d, ⟨2 * k + 1, (1 : ℕ), c + E, d + 2 * k, E⟩ [fm]⊢*
    ⟨2 * (k + E) + 1, 1, c, d + 2 * (k + E), 0⟩ := by
  intro E; induction' E with E ih <;> intro k c d
  · simp; exists 0
  · rw [show c + (E + 1) = (c + E) + 1 from by ring,
        show (E + 1 : ℕ) = E + 1 from rfl]
    step fm  -- R1: (2k+4, 0, c+E, d+2k+1, E+1)
    step fm  -- R2: (2k+3, 1, c+E, d+2k+2, E)
    rw [show d + 2 * k + 1 + 1 = d + 2 * (k + 1) from by ring,
        show 2 * k + 3 = 2 * (k + 1) + 1 from by ring]
    apply stepStar_trans (ih (k + 1) c d)
    ring_nf; finish

-- Main transition: (0, 0, d+g+2, d, 0) ->+ (0, 0, 2d+g+4, 2d+1, 0)
theorem main_trans (d g : ℕ) :
    ⟨(0 : ℕ), 0, d + g + 2, d, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * d + g + 4, 2 * d + 1, 0⟩ := by
  -- Phase 1: R4 x d: drain d to e
  have h1 := d_to_e d (d + g + 2) 0 0
  rw [show (0 : ℕ) + d = d from by ring] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- State: (0, 0, d+g+2, 0, d)
  -- Phase 2: R5
  rw [show d + g + 2 = (d + g + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0, (d + g + 1) + 1, 0, d⟩ : Q) [fm]⊢ ⟨1, 1, d + g + 1, 0, d⟩)
  -- State: (1, 1, d+g+1, 0, d)
  -- Phase 3: R1+R2 chain x d rounds
  have h3 := r1r2_chain d 0 (g + 1) 0
  rw [show g + 1 + d = d + g + 1 from by ring,
      show 0 + 2 * 0 = 0 from by ring,
      show 2 * 0 + 1 = 1 from by ring,
      show 0 + 2 * (0 + d) = 2 * d from by ring,
      show 2 * (0 + d) + 1 = 2 * d + 1 from by ring] at h3
  apply stepStar_trans h3
  -- State: (2d+1, 1, g+1, 2d, 0). R1 fires.
  step fm
  -- State: (2d+1+3, 0, g, 2d+1, 0). R3 drain.
  rw [show 2 * d + 1 + 3 = 0 + (2 * d + 4) from by ring]
  apply stepStar_trans (a_to_c (2 * d + 4) 0 g (2 * d + 1))
  rw [show g + (2 * d + 4) = 2 * d + g + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 1, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, g⟩ ↦ ⟨0, 0, d + (g + 2), d, 0⟩) ⟨1, 0⟩
  intro ⟨d, g⟩
  exists ⟨2 * d + 1, g + 1⟩
  show ⟨(0 : ℕ), 0, d + (g + 2), d, 0⟩ [fm]⊢⁺ ⟨0, 0, (2 * d + 1) + (g + 1 + 2), 2 * d + 1, 0⟩
  rw [show d + (g + 2) = d + g + 2 from by ring,
      show (2 * d + 1) + (g + 1 + 2) = 2 * d + g + 4 from by ring]
  exact main_trans d g

end Sz22_2003_unofficial_1282
