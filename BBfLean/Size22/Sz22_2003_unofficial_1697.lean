import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1697: [77/15, 9/154, 28/3, 5/7, 3/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1 -1
 2 -1  0  1  0
 0  0  1 -1  0
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1697

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1 (R4 chain): d transfers to c
theorem r4_chain : ∀ k, ∀ a c d,
    ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a (c + 1) d)
  ring_nf; finish

-- Combined R1+R2 drain: (a+c, b+1, c, d, d) →* (a, b+c+1, 0, d, d)
theorem r1r2_drain : ∀ c, ∀ a b d,
    ⟨a + c, b + 1, c, d, d⟩ [fm]⊢* ⟨a, b + c + 1, 0, d, d⟩ := by
  intro c; induction' c with c ih <;> intro a b d
  · exists 0
  -- State: (a + (c+1), b+1, c+1, d, d)
  -- R1: (a + c + 1, b, c, d+1, d+1)
  rw [show a + (c + 1) = a + c + 1 from by ring]
  step fm
  -- Now at (a + c + 1, b, c, d+1, d+1). Case split on b.
  rcases b with _ | b'
  · -- b = 0: state is (a + c + 1, 0, c, d+1, d+1). R2 fires.
    rw [show a + c + 1 = (a + c) + 1 from by ring]
    step fm
    -- Now at (a + c, 2, c, d, d) = (a + c, 1+1, c, d, d)
    apply stepStar_trans (ih a 1 d)
    ring_nf; finish
  · -- b = b'+1: state is (a + c + 1, b'+1, c, d+1, d+1)
    -- This matches IH: ((a+1)+c, b'+1, c, (d+1), (d+1))
    rw [show a + c + 1 = (a + 1) + c from by ring]
    apply stepStar_trans (ih (a + 1) b' (d + 1))
    -- After IH: (a+1, b'+c+1, 0, d+1, d+1). R2 fires.
    rw [show (a + 1) = a + 1 from by ring,
        show b' + c + 1 = b' + c + 1 from by ring]
    step fm
    ring_nf; finish

-- Phase 3 (R3 chain): b transfers to a and d
theorem r3_chain : ∀ k, ∀ a d,
    ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih (a + 2) (d + 1))
  ring_nf; finish

-- Main transition: (a+d+2, 0, 0, d+1, 0) ⊢⁺ (a+2*d+4, 0, 0, d+2, 0)
theorem main_trans (a d : ℕ) :
    ⟨a + d + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 4, 0, 0, d + 2, 0⟩ := by
  -- Phase 1: R4 chain, d+1 steps: (a+d+2, 0, 0, d+1, 0) →* (a+d+2, 0, d+1, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + d + 2, 0, d + 1, 0, 0⟩)
  · have h := r4_chain (d + 1) (a + d + 2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R5: (a+d+2, 0, d+1, 0, 0) → (a+d+1, 1, d+1, 0, 0)
  apply step_stepStar_stepPlus (c₂ := ⟨a + d + 1, 1, d + 1, 0, 0⟩)
  · show fm ⟨(a + d + 1) + 1, 0, d + 1, 0, 0⟩ = some ⟨a + d + 1, 0 + 1, d + 1, 0, 0⟩
    simp [fm]
  -- Phase 2: R1+R2 drain: (a+d+1, 1, d+1, 0, 0) →* (a, d+2, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨a, d + 2, 0, 0, 0⟩)
  · have h := r1r2_drain (d + 1) a 0 0
    rw [show a + (d + 1) = a + d + 1 from by ring,
        show 0 + 1 = 1 from by ring,
        show 0 + (d + 1) + 1 = d + 2 from by ring] at h
    exact h
  -- Phase 3: R3 chain: (a, d+2, 0, 0, 0) →* (a+2*(d+2), 0, 0, d+2, 0)
  have h := r3_chain (d + 2) a 0
  rw [show a + 2 * (d + 2) = a + 2 * d + 4 from by ring,
      show 0 + (d + 2) = d + 2 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + d + 2, 0, 0, d + 1, 0⟩) ⟨0, 0⟩
  intro ⟨a, d⟩
  refine ⟨⟨a + d + 1, d + 1⟩, ?_⟩
  show ⟨a + d + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨(a + d + 1) + (d + 1) + 2, 0, 0, (d + 1) + 1, 0⟩
  rw [show (a + d + 1) + (d + 1) + 2 = a + 2 * d + 4 from by ring,
      show (d + 1) + 1 = d + 2 from by ring]
  exact main_trans a d

end Sz22_2003_unofficial_1697
