import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #185: [1/6, 175/2, 4/77, 3/7, 242/15]

Vector representation:
```
-1 -1  0  0  0
-1  0  2  1  0
 2  0  0 -1 -1
 0  1  0 -1  0
 1 -1 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_185

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R4 chain: d → b (when a=0, e=0)
theorem d_to_b : ∀ k b c d, ⟨0, b, c, d + k, 0⟩ [fm]⊢* ⟨(0 : ℕ), b + k, c, d, 0⟩ := by
  intro k; induction k with
  | zero => intro b c d; exists 0
  | succ k ih =>
    intro b c d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- b_pair: R5 then R1, consuming 2 from b and 1 from c
theorem b_pair : ∀ k b c e, ⟨0, b + 2 * k, c + k, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c, 0, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro b c e; exists 0
  | succ k ih =>
    intro b c e
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Spiral: R3 once then R2 twice, repeated E times
-- (0, 0, X, j+1, E) ⊢* (0, 0, X + 4*E, j+1+E, 0)
theorem spiral : ∀ E X j, ⟨0, 0, X, j + 1, E⟩ [fm]⊢* ⟨(0 : ℕ), 0, X + 4 * E, j + 1 + E, 0⟩ := by
  intro E; induction E with
  | zero => intro X j; exists 0
  | succ E ih =>
    intro X j
    rw [show j + 1 + (E + 1) = (j + 1 + E) + 1 from by ring,
        show (E : ℕ) + 1 = E + 1 from by ring]
    -- R3: (0, 0, X, j+1, E+1) → (2, 0, X, j, E)
    step fm
    -- R2: (2, 0, X, j, E) → (1, 0, X+2, j+1, E)
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    -- R2: (1, 0, X+2, j+1, E) → (0, 0, X+4, j+2, E)
    step fm
    -- IH: (0, 0, X+4, (j+1)+1, E) ⊢* (0, 0, X+4+4*E, (j+1)+1+E, 0)
    apply stepStar_trans (ih (X + 4) (j + 1))
    ring_nf; finish

-- Main transition: (0, 0, C+k+1, 2*k+1, 0) ⊢⁺ (0, 0, C+8*k+10, 2*k+3, 0)
theorem main_trans (C k : ℕ) :
    ⟨0, 0, C + k + 1, 2 * k + 1, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, C + 8 * k + 10, 2 * k + 3, 0⟩ := by
  -- Phase 1: d_to_b: (0, 0, C+k+1, 2k+1, 0) →* (0, 2k+1, C+k+1, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2 * k + 1, C + k + 1, 0, 0⟩)
  · have h := d_to_b (2 * k + 1) 0 (C + k + 1) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: b_pair k times: (0, 2k+1, C+k+1, 0, 0) →* (0, 1, C+1, 0, 2k)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, C + 1, 0, 2 * k⟩)
  · have h := b_pair k 1 (C + 1) 0
    rw [show 1 + 2 * k = 2 * k + 1 from by ring,
        show (C + 1) + k = C + k + 1 from by ring,
        show 0 + 2 * k = 2 * k from by ring] at h; exact h
  -- Phase 3: R5: (0, 1, C+1, 0, 2k) → (1, 0, C, 0, 2k+2)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, C, 0, 2 * k + 2⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show C + 1 = C + 1 from by ring,
        show 2 * k + 2 = 2 * k + 2 from by ring]
    show fm ⟨0, 0 + 1, C + 1, 0, 2 * k⟩ = some ⟨1, 0, C, 0, 2 * k + 2⟩
    simp [fm]
  -- Phase 4: R2: (1, 0, C, 0, 2k+2) → (0, 0, C+2, 1, 2k+2)
  apply stepStar_trans (c₂ := ⟨0, 0, C + 2, 1, 2 * k + 2⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm; finish
  -- Phase 5: Spiral: (0, 0, C+2, 1, 2k+2) →* (0, 0, C+2+4*(2k+2), 1+(2k+2), 0)
  --        = (0, 0, C+8k+10, 2k+3, 0)
  · have h := spiral (2 * k + 2) (C + 2) 0
    rw [show (0 : ℕ) + 1 = 1 from by ring] at h
    refine stepStar_trans h ?_
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨C, k⟩ ↦ ⟨0, 0, C + k + 1, 2 * k + 1, 0⟩) ⟨1, 0⟩
  intro ⟨C, k⟩
  refine ⟨⟨C + 7 * k + 8, k + 1⟩, ?_⟩
  show ⟨0, 0, C + k + 1, 2 * k + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, (C + 7 * k + 8) + (k + 1) + 1, 2 * (k + 1) + 1, 0⟩
  rw [show (C + 7 * k + 8) + (k + 1) + 1 = C + 8 * k + 10 from by ring,
      show 2 * (k + 1) + 1 = 2 * k + 3 from by ring]
  exact main_trans C k

end Sz22_2003_unofficial_185
