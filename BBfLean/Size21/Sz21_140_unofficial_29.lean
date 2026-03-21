import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #29: [35/6, 121/2, 28/55, 3/7, 5/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  1 -1
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_29

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- Phase 1: R4 repeated d times: (0, b, 0, d+k, e) →* (0, b+k, 0, d, e)
theorem d_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Interleaved R1,R1,R3 rounds:
-- (2, 2*K+1, j, D, E+K) →* (2, 1, j+K, D+3*K, E)
theorem r1r1r3_rounds : ∀ K, ∀ j D E, ⟨2, 2*K+1, j, D, E+K⟩ [fm]⊢* ⟨2, 1, j+K, D+3*K, E⟩ := by
  intro K; induction' K with K ih <;> intro j D E
  · exists 0
  rw [show 2 * (K + 1) + 1 = (2 * K + 2) + 1 from by ring,
      show E + (K + 1) = (E + K) + 1 from by ring]
  step fm
  rw [show 2 * K + 2 = (2 * K + 1) + 1 from by ring]
  step fm
  rw [show j + 2 = (j + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (j+1) (D+3) E)
  ring_nf; finish

-- R3,R2,R2 chain: (0, 0, c+k, D, E+1) →* (0, 0, c, D+k, E+1+3*k)
theorem r3r2r2_chain : ∀ k, ∀ c D E, ⟨0, 0, c+k, D, E+1⟩ [fm]⊢* ⟨0, 0, c, D+k, E+1+3*k⟩ := by
  intro k; induction' k with k ih <;> intro c D E
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  step fm
  step fm
  rw [show E + 4 = (E + 3) + 1 from by ring]
  apply stepStar_trans (ih c (D+1) (E+3))
  ring_nf; finish

-- Phase 2: (0, 2K+1, 0, 0, K+E+4) →* (0, 0, K+1, 3K+2, E+4)
theorem phase2 (K E : ℕ) : ⟨0, 2*K+1, 0, 0, K+E+4⟩ [fm]⊢* ⟨0, 0, K+1, 3*K+2, E+4⟩ := by
  rw [show K + E + 4 = (K + E + 3) + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨0, 2*K+1, 1, 0, K+E+3⟩)
  · step fm; finish
  rw [show K + E + 3 = (K + E + 2) + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨2, 2*K+1, 0, 1, K+E+2⟩)
  · step fm; finish
  rw [show K + E + 2 = (E + 2) + K from by ring]
  apply stepStar_trans (c₂ := ⟨2, 1, 0+K, 1+3*K, E+2⟩)
  · exact r1r1r3_rounds K 0 1 (E+2)
  simp only [Nat.zero_add]
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 1 + 3 * K = (3 * K) + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨1, 0, K+1, 3*K+2, E+2⟩)
  · step fm; finish
  step fm; ring_nf; finish

-- Main transition: (0,0,0,2K+1,2K+e+4) ⊢⁺ (0,0,0,4K+3,4K+e+7)
theorem main_trans (K e : ℕ) : ⟨0, 0, 0, 2*K+1, 2*K+e+4⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*K+3, 4*K+e+7⟩ := by
  -- Phase 1: R4 repeated (2K+1 times)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*K+1, 0, 0, 2*K+e+4⟩)
  · rw [show 2 * K + 1 = 0 + (2 * K + 1) from by ring]
    exact d_to_b (2*K+1) 0 0
  -- Phase 2: (0, 2K+1, 0, 0, 2K+e+4) →* (0, 0, K+1, 3K+2, K+e+4)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, K+1, 3*K+2, K+e+4⟩)
  · rw [show 2 * K + e + 4 = K + (K + e) + 4 from by ring]
    exact phase2 K (K+e)
  -- Phase 3: first R3 step for stepPlus, then chain for the rest
  -- (0, 0, K+1, 3K+2, K+e+4) with K+1 >= 1 and K+e+4 >= 1
  -- R3: → (2, 0, K, 3K+3, K+e+3)
  apply step_stepStar_stepPlus (c₂ := ⟨2, 0, K, 3*K+3, K+e+3⟩)
  · rw [show K + 1 = K + 1 from rfl,
        show K + e + 4 = (K + e + 3) + 1 from by ring]
    show fm ⟨0, 0, K + 1, 3 * K + 2, (K + e + 3) + 1⟩ = some ⟨2, 0, K, 3 * K + 3, K + e + 3⟩
    simp [fm]
  -- R2,R2: (2, 0, K, 3K+3, K+e+3) → (1, 0, K, 3K+3, K+e+5) → (0, 0, K, 3K+3, K+e+7)
  apply stepStar_trans (c₂ := ⟨0, 0, K, 3*K+3, K+e+7⟩)
  · step fm; step fm; ring_nf; finish
  -- Remaining K rounds of R3,R2,R2
  -- (0, 0, 0+K, 3K+3, (K+e+6)+1) →* (0, 0, 0, 3K+3+K, (K+e+6)+1+3*K)
  rw [show K + e + 7 = (K + e + 6) + 1 from by ring]
  have h := r3r2r2_chain K 0 (3*K+3) (K+e+6)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 4⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨K, e⟩ ↦ ⟨0, 0, 0, 2*K+1, 2*K+e+4⟩) ⟨0, 0⟩
  intro ⟨K, e⟩; simp only []
  refine ⟨⟨2*K+1, e+1⟩, ?_⟩; simp only []
  have h := main_trans K e
  convert h using 2; ring_nf

end Sz21_140_unofficial_29
