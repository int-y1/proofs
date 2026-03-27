import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #88: [1/30, 147/2, 6/77, 15/7, 22/3]

Vector representation:
```
-1 -1 -1  0  0
-1  1  0  2  0
 1  1  0 -1 -1
 0  1  1 -1  0
 1 -1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_88

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- Phase 2: E pairs of (R2, R1): (0, B, 0, 2, E+1) →* (0, B+2*E, 0, E+2, 1)
-- Generalized: (0, B, 0, D+2, K+1) with K pairs → (0, B+2*K, 0, D+K+2, 1)
theorem r2r1_chain : ∀ K, ∀ B D, ⟨0, B, 0, D + 2, K + 1⟩ [fm]⊢* ⟨0, B + 2 * K, 0, D + K + 2, 1⟩ := by
  intro K; induction' K with K ih <;> intro B D
  · exists 0
  rw [show K + 1 + 1 = (K + 1) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih (B + 2) (D + 1))
  ring_nf; finish

-- Phase 4: R3 chain: (0, B, 0, D, 0) →* (0, B+D, D, 0, 0)
-- Actually: (0, B, C, D, 0) →* (0, B+D, C+D, 0, 0)
theorem r3_chain : ∀ D, ∀ B C, ⟨0, B, C, D, 0⟩ [fm]⊢* ⟨0, B + D, C + D, 0, 0⟩ := by
  intro D; induction' D with D ih <;> intro B C
  · exists 0
  rw [show (D + 1) = D + 1 from rfl]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 5: (R4, R0) chain: (0, B+2*K, K, 0, E) with K pairs → (0, B, 0, 0, E+K)
-- Generalized: ∀ K B E, (0, B+2*K, K, 0, E) →* (0, B, 0, 0, E+K)
theorem r4r0_chain : ∀ K, ∀ B E, ⟨0, B + 2 * K, K, 0, E⟩ [fm]⊢* ⟨0, B, 0, 0, E + K⟩ := by
  intro K; induction' K with K ih <;> intro B E
  · exists 0
  rw [show B + 2 * (K + 1) = (B + 2 * K) + 1 + 1 from by ring,
      show K + 1 = K + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Main transition: (0, B, 0, 0, E) →⁺ (0, B+E-1, 0, 0, E+3) for B ≥ 1, E ≥ 2
-- We write E = E'+2, B = B'+1 to avoid subtraction.
theorem main_trans : ⟨0, B + 1, 0, 0, E + 2⟩ [fm]⊢⁺ ⟨0, B + E + 2, 0, 0, E + 5⟩ := by
  -- Phase 1: R4, R1: (0, B+1, 0, 0, E+2) → (1, B, 0, 0, E+3) → (0, B+1, 0, 2, E+3)
  step fm; step fm
  -- Phase 2: R2/R1 chain with E+2 pairs
  -- State: (0, B+1, 0, 2, E+3) = (0, B+1, 0, 0+2, (E+2)+1)
  -- After E+2 pairs: (0, B+1+2*(E+2), 0, 0+(E+2)+2, 1) = (0, B+2*E+5, 0, E+4, 1)
  rw [show E + 3 = (E + 2) + 1 from by ring]
  apply stepStar_trans (r2r1_chain (E + 2) (B + 1) 0)
  -- State: (0, B+2*E+5, 0, E+4, 1)
  -- Phase 3: R2, R1: → (1, B+2*E+6, 0, E+3, 0) → (0, B+2*E+7, 0, E+5, 0)
  rw [show B + 1 + 2 * (E + 2) = B + 2 * E + 5 from by ring,
      show 0 + (E + 2) + 2 = (E + 4) from by ring,
      show (E + 4) = (E + 3) + 1 from by ring]
  step fm; step fm
  -- State: (0, B+2*E+7, 0, E+5, 0)
  -- Phase 4: R3 chain with E+5 steps → (0, B+3*E+12, E+5, 0, 0)
  apply stepStar_trans (r3_chain (E + 5) (B + 2 * E + 7) 0)
  -- State: (0, B+3*E+12, E+5, 0, 0)
  -- Phase 5: R4/R0 chain with E+5 pairs → (0, B+E+2, 0, 0, E+5)
  rw [show B + 2 * E + 7 + (E + 5) = (B + E + 2) + 2 * (E + 5) from by ring,
      show 0 + (E + 5) = E + 5 from by ring]
  apply stepStar_trans (r4r0_chain (E + 5) (B + E + 2) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 2⟩) (by execute fm 17)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨B, E⟩ ↦ ⟨0, B + 1, 0, 0, E + 2⟩) ⟨0, 0⟩
  intro ⟨B, E⟩; exact ⟨⟨B + E + 1, E + 3⟩, main_trans⟩

end Sz22_2003_unofficial_88
