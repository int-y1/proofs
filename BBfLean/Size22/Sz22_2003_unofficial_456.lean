import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #456: [28/15, 11/3, 33/2, 5/847, 14/11]

Vector representation:
```
 2 -1 -1  1  0
 0 -1  0  0  1
-1  1  0  0  1
 0  0  1 -1 -2
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_456

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Phase 1: R1,R3 interleaved chain
-- (A, 1, K, D, E) →* (A+K, 1, 0, D+K, E+K)
theorem r1r3_chain : ∀ K, ∀ A D E, ⟨A, 1, K, D, E⟩ [fm]⊢* ⟨A+K, 1, 0, D+K, E+K⟩ := by
  intro K; induction' K with K h <;> intro A D E
  · exists 0
  step fm; step fm
  apply stepStar_trans (h (A + 1) (D + 1) (E + 1))
  ring_nf; finish

-- Phase 2: R3,R2 drain chain
-- (K, 0, 0, D, E) →* (0, 0, 0, D, E+2*K)
theorem r3r2_drain : ∀ K, ∀ D E, ⟨K, 0, 0, D, E⟩ [fm]⊢* ⟨0, 0, 0, D, E+2*K⟩ := by
  intro K; induction' K with K h <;> intro D E
  · exists 0
  step fm; step fm
  apply stepStar_trans (h D (E + 2))
  ring_nf; finish

-- Phase 3: R4 chain
-- (0, 0, C, D+K, E+2*K) →* (0, 0, C+K, D, E)
theorem r4_chain : ∀ K, ∀ C D E, ⟨0, 0, C, D+K, E+2*K⟩ [fm]⊢* ⟨0, 0, C+K, D, E⟩ := by
  intro K; induction' K with K h <;> intro C D E
  · exists 0
  rw [show D + (K + 1) = (D + K) + 1 from by ring,
      show E + 2 * (K + 1) = (E + 2 * K) + 2 from by ring]
  step fm
  apply stepStar_trans (h (C + 1) D E)
  ring_nf; finish

-- Combined phase: opening + R1R3 chain + R2
-- (0, 0, c+1, 0, e+1) →* (c+1, 0, 0, c+2, e+c+3)
-- Decomposed as: R5, R3, then c+1 R1R3 rounds, then R2
theorem opening_and_chain (c e : ℕ) :
    ⟨0, 0, c+1, 0, e+1⟩ [fm]⊢⁺ ⟨c+1, 0, 0, c+2, e+c+3⟩ := by
  -- R5: → (1, 0, c+1, 1, e)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, c+1, 1, e⟩)
  · show fm ⟨0, 0, c+1, 0, e+1⟩ = some ⟨1, 0, c+1, 1, e⟩; simp [fm]
  -- R3: → (0, 1, c+1, 1, e+1)
  -- R1,R3 chain: → (c+1, 1, 0, c+2, e+c+2)
  apply stepStar_trans (c₂ := ⟨c+1, 1, 0, c+2, e+c+2⟩)
  · apply stepStar_trans (c₂ := ⟨0, 1, c+1, 1, e+1⟩)
    · step fm; finish
    have h := r1r3_chain (c+1) 0 1 (e+1)
    simp only [Nat.zero_add] at h
    rw [show 1 + (c + 1) = c + 2 from by omega,
        show e + 1 + (c + 1) = e + c + 2 from by omega] at h
    exact h
  -- R2: → (c+1, 0, 0, c+2, e+c+3)
  step fm
  rw [show e + c + 2 + 1 = e + c + 3 from by omega]
  finish

-- Main transition: (0, 0, c+1, 0, e+1) →⁺ (0, 0, c+2, 0, e+c+1)
theorem main_trans (c e : ℕ) : ⟨0, 0, c+1, 0, e+1⟩ [fm]⊢⁺ ⟨0, 0, c+2, 0, e+c+1⟩ := by
  apply stepPlus_stepStar_stepPlus (opening_and_chain c e)
  -- R3,R2 drain (c+1 rounds): (c+1, 0, 0, c+2, e+c+3) →* (0, 0, 0, c+2, e+3*c+5)
  apply stepStar_trans (c₂ := ⟨0, 0, 0, c+2, e+3*c+5⟩)
  · rw [show e + 3 * c + 5 = (e + c + 3) + 2 * (c + 1) from by omega]
    exact r3r2_drain (c+1) (c+2) (e+c+3)
  -- R4 chain (c+2 rounds): (0, 0, 0, c+2, e+3*c+5) →* (0, 0, c+2, 0, e+c+1)
  rw [show (0 : ℕ) = 0 + 0 from by omega,
      show c + 2 = 0 + (c + 2) from by omega,
      show e + 3 * c + 5 = (e + c + 1) + 2 * (c + 2) from by omega]
  exact r4_chain (c+2) 0 0 (e+c+1)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 1⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, e⟩ ↦ ⟨0, 0, c+1, 0, e+1⟩) ⟨0, 0⟩
  intro ⟨c, e⟩; exact ⟨⟨c+1, e+c⟩, main_trans c e⟩
