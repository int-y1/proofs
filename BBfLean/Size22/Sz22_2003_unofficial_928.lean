import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #928: [4/15, 33/14, 25/2, 7/11, 14/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_928

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Phase: R2/R1 interleaved chain
-- From (a, 1, c+d+1, d, e) to (a+d, 1, c+1, 0, e+d)
-- Each round: R1 consumes b and c, then R2 consumes a and d
-- Actually: from (1, 0, c+d, d, 0) we first apply R2 to get (0, 1, c+d, d-1, 1),
-- then R1 to get (2, 0, c+d-1, d-1, 1), etc.
-- Net per round: a stays at start+round, c decreases by 1, d decreases by 1, e increases by 1
-- Let's prove: (a, 1, c+d+1, d, e) ⊢* (a+d, 1, c+1, 0, e+d)
theorem r1r2_chain : ∀ d, ∀ a c e,
    ⟨a, 1, c + d + 1, d, e⟩ [fm]⊢* ⟨a + d, 1, c + 1, 0, e + d⟩ := by
  intro d; induction' d with d ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + (d + 1) + 1 = (c + d + 1) + 1 from by ring,
        show (d : ℕ) + 1 = d + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

-- Phase: R3 drain (consumes a, adds 2 to c per step)
-- From (k, 0, c, 0, e) to (0, 0, c+2*k, 0, e)
theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) e); ring_nf; finish

-- Phase: R4 drain (transfers e to d)
-- From (0, 0, c, d, k) to (0, 0, c, d+k, 0)
theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

-- Main transition: (1, 0, c+d, d, 0) ⊢⁺ (1, 0, c+2*d+1, d+1, 0)
-- Phases:
--   D=0: R3(1 step) then R5(c+2 steps giving) ... simpler path
--   D>0: R2 kick, R1/R2 chain, final R1, R3 drain, R4 drain, R5 kick
theorem main_trans (c d : ℕ) :
    ⟨1, 0, c + d, d, 0⟩ [fm]⊢⁺ ⟨1, 0, c + 2 * d + 1, d + 1, 0⟩ := by
  rcases d with _ | d
  · -- d = 0: state is (1, 0, c, 0, 0)
    -- R3: (1, 0, c, 0, 0) → (0, 0, c+2, 0, 0)
    -- R5: (0, 0, c+2, 0, 0) → (1, 0, c+1, 1, 0)
    simp only [Nat.add_zero, Nat.mul_zero]
    apply step_stepStar_stepPlus
    · show fm ⟨1, 0, c, 0, 0⟩ = some ⟨0, 0, c + 2, 0, 0⟩; unfold fm; simp only
    · apply step_stepStar
      show fm ⟨0, 0, c + 2, 0, 0⟩ = some ⟨1, 0, c + 1, 1, 0⟩; unfold fm; simp only
  · -- d+1 > 0: state is (1, 0, c + (d+1), d+1, 0)
    -- Phase 1: R2 kick: (1, 0, c+d+1, d+1, 0) → (0, 1, c+d+1, d, 1)
    have h1 : ⟨1, 0, c + (d + 1), d + 1, 0⟩ [fm]⊢⁺
        ⟨0, 1, c + (d + 1), d, 1⟩ := by
      apply step_stepPlus
      show fm ⟨1, 0, c + (d + 1), d + 1, 0⟩ = some ⟨0, 1, c + (d + 1), d, 1⟩
      unfold fm; simp only
    -- Phase 2: R1/R2 chain: (0, 1, c+d+1, d, 1) ⊢* (d, 1, c+1, 0, d+1)
    have h2 : ⟨0, 1, c + (d + 1), d, 1⟩ [fm]⊢*
        ⟨d, 1, c + 1, 0, d + 1⟩ := by
      have := r1r2_chain d 0 c 1
      rw [show c + d + 1 = c + (d + 1) from by ring,
          show 0 + d = d from by ring,
          show 1 + d = d + 1 from by ring] at this
      exact this
    -- Phase 3: Final R1: (d, 1, c+1, 0, d+1) → (d+2, 0, c, 0, d+1)
    have h3 : ⟨d, 1, c + 1, 0, d + 1⟩ [fm]⊢*
        ⟨d + 2, 0, c, 0, d + 1⟩ := by
      rw [show c + 1 = c + 1 from rfl]
      apply step_stepStar
      show fm ⟨d, 1, c + 1, 0, d + 1⟩ = some ⟨d + 2, 0, c, 0, d + 1⟩
      unfold fm; simp only
    -- Phase 4: R3 drain: (d+2, 0, c, 0, d+1) ⊢* (0, 0, c+2*(d+2), 0, d+1)
    have h4 : ⟨d + 2, 0, c, 0, d + 1⟩ [fm]⊢*
        ⟨0, 0, c + 2 * (d + 2), 0, d + 1⟩ := by
      exact r3_drain (d + 2) c (d + 1)
    -- Phase 5: R4 drain: (0, 0, c+2d+4, 0, d+1) ⊢* (0, 0, c+2d+4, d+1, 0)
    have h5 : ⟨0, 0, c + 2 * (d + 2), 0, d + 1⟩ [fm]⊢*
        ⟨0, 0, c + 2 * (d + 2), d + 1, 0⟩ := by
      have := r4_drain (d + 1) (c + 2 * (d + 2)) 0
      rw [show 0 + (d + 1) = d + 1 from by ring] at this
      exact this
    -- Phase 6: R5 kick: (0, 0, c+2d+4, d+1, 0) → (1, 0, c+2d+3, d+2, 0)
    have h6 : ⟨0, 0, c + 2 * (d + 2), d + 1, 0⟩ [fm]⊢*
        ⟨1, 0, c + 2 * d + 3, d + 2, 0⟩ := by
      rw [show c + 2 * (d + 2) = (c + 2 * d + 3) + 1 from by ring]
      apply step_stepStar
      show fm ⟨0, 0, (c + 2 * d + 3) + 1, d + 1, 0⟩ = some ⟨1, 0, c + 2 * d + 3, d + 2, 0⟩
      unfold fm; simp only
    -- Compose: need to show (1, 0, c+d+1, d+1, 0) ⊢⁺ (1, 0, c+2*d+3, d+2, 0)
    -- which equals (1, 0, c+2*(d+1)+1, (d+1)+1, 0)
    rw [show d + 1 + 1 = d + 2 from by ring,
        show c + 2 * (d + 1) + 1 = c + 2 * d + 3 from by ring]
    exact stepPlus_stepStar_stepPlus h1
      (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, d⟩ ↦ ⟨1, 0, c + d, d, 0⟩) ⟨0, 0⟩
  intro ⟨c, d⟩
  refine ⟨⟨c + d, d + 1⟩, ?_⟩
  show ⟨1, 0, c + d, d, 0⟩ [fm]⊢⁺ ⟨1, 0, (c + d) + (d + 1), d + 1, 0⟩
  rw [show (c + d) + (d + 1) = c + 2 * d + 1 from by ring]
  exact main_trans c d

end Sz22_2003_unofficial_928
