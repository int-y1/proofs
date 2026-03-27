import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #12: [1/105, 9/22, 50/3, 7/2, 363/7]

Vector representation:
```
 0 -1 -1 -1  0
-1  2  0  0 -1
 1 -1  2  0  0
-1  0  0  1  0
 0  1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_12

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- Phase 1: R5/R1 drain pairs.
theorem r5r1_drain : ∀ k, ∀ c e, ⟨0, 0, c+k, 2*k+1, e⟩ [fm]⊢* ⟨0, 0, c, 1, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 1b: R5 then R3 bridge.
theorem r5_r3_bridge : ⟨0, 0, c, 1, e⟩ [fm]⊢* ⟨1, 0, c+2, 0, e+2⟩ := by
  step fm; step fm; finish

-- Phase 2: R2/R3 interleave.
theorem r2r3_chain : ∀ E, ∀ b c, ⟨1, b, c, 0, E⟩ [fm]⊢* ⟨1, b+E, c+2*E, 0, 0⟩ := by
  intro E; induction' E with E ih <;> intro b c
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 3: R3 chain.
theorem r3_chain : ∀ k, ∀ a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a+k, 0, c+2*k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 4: R4 chain.
theorem r4_chain : ∀ k, ∀ c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Main transition: (0, 0, c+N+1, 2*N+3, 0) ⊢⁺ (0, 0, c+8*N+18, 2*N+5, 0)
-- Here c is the "excess" beyond N+1.
theorem main_trans (c N : ℕ) :
    ⟨0, 0, c+N+1, 2*N+3, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, c+8*N+18, 2*N+5, 0⟩ := by
  -- Phase 1: R5/R1 drain with k = N+1
  rw [show 2*N+3 = 2*(N+1)+1 from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_drain (N+1) c 0)
  simp only [Nat.zero_add]
  -- Phase 1b: R5 then R3
  apply stepStar_stepPlus_stepPlus (r5_r3_bridge)
  -- Phase 2: R2/R3 chain with E = 2*N+4
  rw [show 2*(N+1)+2 = 2*N+4 from by ring]
  apply stepStar_stepPlus_stepPlus (r2r3_chain (2*N+4) 0 (c+2))
  simp only [Nat.zero_add]
  -- Phase 3: R3 chain
  apply stepStar_stepPlus_stepPlus (r3_chain (2*N+4) 1 (c+2+2*(2*N+4)))
  -- Phase 4: R4 chain
  rw [show 1 + (2*N+4) = 2*N+5 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨2*N+5, 0, c+2+2*(2*N+4)+2*(2*N+4), 0, 0⟩ = some ⟨2*N+4, 0, c+2+2*(2*N+4)+2*(2*N+4), 1, 0⟩
    simp [fm]
  apply stepStar_trans (r4_chain (2*N+4) (c+2+2*(2*N+4)+2*(2*N+4)) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 10, 3, 0⟩) (by execute fm 12)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c N, q = ⟨0, 0, c+N+1, 2*N+3, 0⟩)
  · intro q ⟨c, N, hq⟩; subst hq
    exact ⟨⟨0, 0, c+8*N+18, 2*N+5, 0⟩,
           ⟨c+7*N+16, N+1, by ring_nf⟩,
           main_trans c N⟩
  · exact ⟨9, 0, by ring_nf⟩
