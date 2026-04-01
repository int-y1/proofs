import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1477: [7/15, 4/3, 99/14, 5/11, 363/2]

Vector representation:
```
 0 -1 -1  1  0
 2 -1  0  0  0
-1  2  0 -1  1
 0  0  1  0 -1
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1477

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R4 chain: transfer e to c
theorem e_to_c : ∀ k c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c e; exists 0
  · intro c e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

-- Middle loop: (R3, R1, R1) x k
theorem middle_loop : ∀ k, ∀ A d e, ⟨A + k + 1, 0, c + 2 * k + 1, d + 1, e⟩ [fm]⊢*
    ⟨A + 1, 0, c + 1, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih
  · intro A d e; exists 0
  · intro A d e
    rw [show A + (k + 1) + 1 = (A + k + 1) + 1 from by ring,
        show c + 2 * (k + 1) + 1 = (c + 2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih A (d + 1) (e + 1))
    ring_nf; finish

-- Drain: (R3, R2, R2) x (k+1) rounds
theorem drain_r3r2r2 : ∀ k, ∀ A e, ⟨A + 1, 0, 0, k + 1, e⟩ [fm]⊢*
    ⟨A + 3 * k + 4, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih
  · intro A e; step fm; step fm; step fm; ring_nf; finish
  · intro A e
    rw [show (k + 1) + 1 = k + 1 + 1 from rfl]
    step fm; step fm; step fm
    rw [show A + 2 + 2 = (A + 3) + 1 from by ring]
    apply stepStar_trans (ih (A + 3) (e + 1))
    ring_nf; finish

-- Phases 2-5: R5, R1, middle_loop, R3, R1, R2
theorem phases_2_to_5 (F e : ℕ) :
    ⟨F + e + 2, 0, 2 * e + 2, 0, 0⟩ [fm]⊢⁺ ⟨F + 2, 0, 0, e + 1, e + 3⟩ := by
  -- R5
  rw [show F + e + 2 = (F + e + 1) + 1 from by ring]
  step fm
  -- R1
  rw [show 2 * e + 2 = (2 * e + 1) + 1 from by ring]
  step fm
  -- Middle loop
  have hmid := middle_loop e F 0 2 (c := 0)
  have hmid' : ⟨F + e + 1, 0, 2 * e + 1, 1, 2⟩ [fm]⊢* ⟨F + 1, 0, 1, e + 1, e + 2⟩ := by
    rw [show (0 : ℕ) + 2 * e + 1 = 2 * e + 1 from by ring,
        show (0 : ℕ) + 1 = 1 from by ring,
        show (0 : ℕ) + e + 1 = e + 1 from by ring,
        show (2 : ℕ) + e = e + 2 from by ring] at hmid
    exact hmid
  apply stepStar_trans hmid'
  -- R3, R1, R2: (F+1, 0, 1, e+1, e+2) -> (F+2, 0, 0, e+1, e+3)
  step fm; step fm; step fm; finish

-- Full transition
theorem main_trans (F e : ℕ) :
    ⟨F + e + 2, 0, 0, 0, 2 * e + 2⟩ [fm]⊢⁺ ⟨F + 3 * e + 5, 0, 0, 0, 2 * e + 4⟩ := by
  -- Phase 1: R4 chain
  have h1 := e_to_c (2 * e + 2) 0 0 (a := F + e + 2)
  -- h1 : (F+e+2, 0, 0, 0, 0+(2*e+2)) ⊢* (F+e+2, 0, 0+(2*e+2), 0, 0)
  have h1' : ⟨F + e + 2, 0, 0, 0, 2 * e + 2⟩ [fm]⊢* ⟨F + e + 2, 0, 2 * e + 2, 0, 0⟩ := by
    convert h1 using 2; ring_nf
  apply stepStar_stepPlus_stepPlus h1'
  -- Phases 2-5
  apply stepPlus_stepStar_stepPlus (phases_2_to_5 F e)
  -- Phase 6: drain
  have h6 := drain_r3r2r2 e (F + 1) (e + 3)
  have h6' : ⟨F + 2, 0, 0, e + 1, e + 3⟩ [fm]⊢* ⟨F + 3 * e + 5, 0, 0, 0, 2 * e + 4⟩ := by
    convert h6 using 2; ring_nf
  exact h6'

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, e⟩ ↦ ⟨F + e + 2, 0, 0, 0, 2 * e + 2⟩) ⟨0, 0⟩
  intro ⟨F, e⟩
  refine ⟨⟨F + 2 * e + 2, e + 1⟩, ?_⟩
  show ⟨F + e + 2, 0, 0, 0, 2 * e + 2⟩ [fm]⊢⁺
    ⟨(F + 2 * e + 2) + (e + 1) + 2, 0, 0, 0, 2 * (e + 1) + 2⟩
  rw [show (F + 2 * e + 2) + (e + 1) + 2 = F + 3 * e + 5 from by ring,
      show 2 * (e + 1) + 2 = 2 * e + 4 from by ring]
  exact main_trans F e

end Sz22_2003_unofficial_1477
