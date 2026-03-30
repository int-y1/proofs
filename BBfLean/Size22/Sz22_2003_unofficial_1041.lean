import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1041: [45/2, 4/21, 11/3, 49/55, 3/77]

Vector representation:
```
-1  2  1  0  0
 2 -1  0 -1  0
 0 -1  0  0  1
 0  0 -1  2 -1
 0  1  0 -1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1041

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- One R2R1R1 round: (0, b+1, c, d+1, e) -> (0, b+4, c+2, d, e)
theorem r2r1r1_step (b c d e : ℕ) :
    ⟨(0 : ℕ), b + 1, c, d + 1, e⟩ [fm]⊢* ⟨0, b + 4, c + 2, d, e⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- k rounds of R2R1R1: drain d from k to 0
theorem r2r1r1_chain : ∀ k, ∀ b c e,
    ⟨(0 : ℕ), b + 1, c, k, e⟩ [fm]⊢* ⟨0, b + 1 + 3 * k, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · ring_nf; finish
  · rw [show b + 1 + 3 * (k + 1) = (b + 3) + 1 + 3 * k from by ring,
        show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    apply stepStar_trans (r2r1r1_step b c k e)
    exact ih (b + 3) (c + 2) e

-- R3 chain: drain b, increase e
theorem r3_chain : ∀ k, ∀ c e,
    ⟨(0 : ℕ), k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih c (e + 1))
    ring_nf; finish

-- R4 chain: drain c and e simultaneously, increase d
theorem r4_chain : ∀ k, ∀ d e,
    ⟨(0 : ℕ), 0, k, d, e + k⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show (k + 1) = k + 1 from rfl,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm
    exact ih (d + 2) e

-- Main transition: (0,0,0,D+2,E+1) ⊢⁺ (0,0,0,4D+4,E+D+2)
theorem main_trans (D E : ℕ) :
    ⟨(0 : ℕ), 0, 0, D + 2, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * D + 4, E + D + 2⟩ := by
  -- Phase 1: R5 step
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, D + 2, E + 1⟩ = some ⟨0, 1, 0, D + 1, E⟩
    unfold fm; simp
  -- Phase 2: R2R1R1 chain for D+1 rounds
  have h2 : ⟨(0 : ℕ), 1, 0, D + 1, E⟩ [fm]⊢*
      ⟨0, 3 * D + 4, 2 * D + 2, 0, E⟩ := by
    have := r2r1r1_chain (D + 1) 0 0 E
    rw [show 0 + 1 + 3 * (D + 1) = 3 * D + 4 from by ring,
        show 0 + 2 * (D + 1) = 2 * D + 2 from by ring] at this
    exact this
  -- Phase 3: R3 chain for 3D+4 rounds
  have h3 : ⟨(0 : ℕ), 3 * D + 4, 2 * D + 2, 0, E⟩ [fm]⊢*
      ⟨0, 0, 2 * D + 2, 0, E + (3 * D + 4)⟩ :=
    r3_chain (3 * D + 4) (2 * D + 2) E
  -- Phase 4: R4 chain for 2D+2 rounds
  have h4 : ⟨(0 : ℕ), 0, 2 * D + 2, 0, E + (3 * D + 4)⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * D + 4, E + D + 2⟩ := by
    have := r4_chain (2 * D + 2) 0 (E + D + 2)
    rw [show (E + D + 2) + (2 * D + 2) = E + (3 * D + 4) from by ring,
        show 0 + 2 * (2 * D + 2) = 4 * D + 4 from by ring] at this
    exact this
  exact stepStar_trans h2 (stepStar_trans h3 h4)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨D, E⟩ ↦ ⟨0, 0, 0, D + 2, E + 1⟩) ⟨0, 0⟩
  intro ⟨D, E⟩
  exact ⟨⟨4 * D + 2, E + D + 1⟩, main_trans D E⟩

end Sz22_2003_unofficial_1041
