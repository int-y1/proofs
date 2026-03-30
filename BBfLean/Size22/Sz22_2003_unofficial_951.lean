import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #951: [4/15, 33/14, 275/2, 7/11, 6/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_951

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R1+R2 chain: d rounds of alternating R1 then R2
-- From (a+1, 1, c+d, d, e) → (a+d+1, 1, c, 0, e+d)
theorem r1r2_chain : ∀ k, ∀ a c e,
    ⟨a + 1, 1, c + k, k, e⟩ [fm]⊢* ⟨a + k + 1, 1, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1))
    ring_nf; finish

-- R3 chain: a rounds of R3
-- From (a, 0, c, 0, e) → (0, 0, c + 2*a, 0, e + a)
theorem r3_chain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 2) (e + 1))
    ring_nf; finish

-- R4 chain: e rounds of R4
-- From (0, 0, c, d, e) → (0, 0, c, d + e, 0)
theorem r4_chain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

-- Main transition: (0, 0, d + g + 2, d, 0) →⁺ (0, 0, 2*d + g + 6, 2*d + 3, 0)
theorem main_trans (g d : ℕ) :
    ⟨0, 0, d + g + 2, d, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * d + g + 6, 2 * d + 3, 0⟩ := by
  -- Phase 1: R5
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, d + g + 2, d, 0⟩ = some ⟨1, 1, d + g + 1, d, 0⟩
    simp [fm]
  -- Phase 2: d rounds of R1+R2
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show d + g + 1 = (g + 1) + d from by ring]
  apply stepStar_trans (r1r2_chain d 0 (g + 1) 0)
  rw [show 0 + d + 1 = d + 1 from by ring,
      show 0 + d = d from by ring]
  -- Phase 3: R1 (b=1, c=g+1≥1)
  rw [show g + 1 = g + 1 from rfl]
  step fm
  rw [show d + 1 + 2 = d + 3 from by ring]
  -- Phase 4: R3 fires d+3 times
  apply stepStar_trans (r3_chain (d + 3) g d)
  rw [show g + 2 * (d + 3) = 2 * d + g + 6 from by ring,
      show d + (d + 3) = 2 * d + 3 from by ring]
  -- Phase 5: R4 fires 2*d+3 times
  apply stepStar_trans (r4_chain (2 * d + 3) (2 * d + g + 6) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 7, 5, 0⟩) (by execute fm 15)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨g, d⟩ ↦ ⟨0, 0, d + g + 2, d, 0⟩) ⟨0, 5⟩
  intro ⟨g, d⟩
  refine ⟨⟨g + 1, 2 * d + 3⟩, ?_⟩
  convert main_trans g d using 2
  · ring_nf

end Sz22_2003_unofficial_951
