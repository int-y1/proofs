import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1593: [77/15, 1/154, 9/7, 4/3, 175/2]

Vector representation:
```
 0 -1 -1  1  1
-1  0  0 -1 -1
 0  2  0 -1  0
 2 -1  0  0  0
-1  0  2  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1593

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

-- R3 chain: (0, b, 0, d+k, e) →* (0, b+2k, 0, d, e)
theorem d_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih (b + 2) d)
    ring_nf; finish

-- R4 chain: (a, b+k, 0, 0, e) →* (a+2k, b, 0, 0, e)
theorem b_to_a : ∀ k, ∀ a b, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih (a + 2) b)
    ring_nf; finish

-- Full R5/R2 drain: (4+2k, 0, c, 0, k) →* (4, 0, c+2k, 0, 0)
theorem full_drain : ∀ k, ∀ c, ⟨4 + 2 * k, 0, c, 0, k⟩ [fm]⊢* ⟨4, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show 4 + 2 * (k + 1) = (4 + 2 * k) + 1 + 1 from by omega,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    step fm
    apply stepStar_trans (ih (c + 2))
    ring_nf; finish

-- Tail: (4, 0, c, 0, 0) →⁺ (0, 0, c, 2, 2)
theorem tail : ⟨4, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, c, 2, 2⟩ := by
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm
  finish

-- R3/R1/R1 chain: (0, 0, c+2k, d+1, e) →* (0, 0, c, d+k+1, e+2k)
theorem r3r1r1_chain : ∀ k, ∀ c d e, ⟨0, 0, c + 2 * k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + k + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by omega]
    step fm
    step fm
    step fm
    rw [show d + 2 = (d + 1) + 1 from by omega]
    apply stepStar_trans (ih c (d + 1) (e + 2))
    ring_nf; finish

-- Main transition: (0, 0, 0, D+2, 2*D+2) →⁺ (0, 0, 0, 2*D+4, 4*D+6)
theorem main_trans (D : ℕ) : ⟨0, 0, 0, D + 2, 2 * D + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * D + 4, 4 * D + 6⟩ := by
  -- Phase 1: d_to_b. Rewrite to match d_to_b signature.
  rw [show D + 2 = 0 + (D + 2) from by omega]
  apply stepStar_stepPlus_stepPlus (d_to_b (e := 2 * D + 2) (D + 2) 0 0)
  -- Now at: (0, 2*(D+2), 0, 0, 2D+2)
  -- Phase 2: b_to_a. Rewrite to match b_to_a signature.
  rw [show 0 + 2 * (D + 2) = 0 + (2 * D + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (b_to_a (e := 2 * D + 2) (2 * D + 4) 0 0)
  -- Now at: (4D+8, 0, 0, 0, 2D+2)
  -- Phase 3: full_drain. Rewrite to match full_drain signature.
  rw [show 0 + 2 * (2 * D + 4) = 4 + 2 * (2 * D + 2) from by ring,
      show (2 * D + 2 : ℕ) = 2 * D + 2 from rfl]
  apply stepStar_stepPlus_stepPlus (full_drain (2 * D + 2) 0)
  -- Now at: (4, 0, 4D+4, 0, 0)
  rw [show 0 + 2 * (2 * D + 2) = 4 * D + 4 from by ring]
  -- Phase 4: tail
  apply stepPlus_stepStar_stepPlus (tail (c := 4 * D + 4))
  -- Now at: (0, 0, 4D+4, 2, 2)
  -- Phase 5: r3r1r1_chain
  rw [show (4 * D + 4 : ℕ) = 0 + 2 * (2 * D + 2) from by ring,
      show (2 : ℕ) = 1 + 1 from by omega]
  apply stepStar_trans (r3r1r1_chain (2 * D + 2) 0 1 2)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun D ↦ ⟨0, 0, 0, D + 2, 2 * D + 2⟩) 0
  intro D; refine ⟨2 * D + 2, ?_⟩
  rw [show 2 * D + 2 + 2 = 2 * D + 4 from by omega,
      show 2 * (2 * D + 2) + 2 = 4 * D + 6 from by ring]
  exact main_trans D
