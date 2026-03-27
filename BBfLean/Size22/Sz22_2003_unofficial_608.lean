import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #608: [35/6, 121/2, 4/55, 3/7, 75/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 0  1  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_608

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+2, d, e⟩
  | _ => none

-- R4 chain: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _); ring_nf; finish

-- R3+R2+R2 drain: each round converts 1 unit of c into 3 units of e
theorem drain : ∀ k c d e, ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e + 3*k + 1⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- Full process: interleave R3+R1R1 rounds then drain
-- (0, B, c+1, d, e+B+1) ->* (0, 0, 0, d+B, e + 3*c + 2*B + 4)
theorem process : ∀ B, ∀ c d e,
    ⟨0, B, c+1, d, e+B+1⟩ [fm]⊢* ⟨0, 0, 0, d+B, e + 3*c + 2*B + 4⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro c d e
  rcases B with _ | _ | B
  · -- B=0: drain c+1 rounds
    have h := drain (c+1) 0 d e
    rw [Nat.zero_add] at h
    apply stepStar_trans h; ring_nf; finish
  · -- B=1: R3, R1, R2, then drain c+1 rounds
    step fm; step fm; step fm
    have h := drain (c+1) 0 (d+1) (e+2)
    rw [Nat.zero_add] at h
    apply stepStar_trans h; ring_nf; finish
  · -- B+2: R3, R1, R1, then IH on B
    rw [show e + (B + 2) + 1 = (e + 2) + B + 1 from by ring]
    step fm; step fm; step fm
    -- After 3 steps: (0, B, c+2, d+2, (e+2)+B)
    -- Need: (e+2)+B = (e+1)+B+1
    rw [show c + 2 = (c + 1) + 1 from by ring]
    rw [show e + 2 + B = (e + 1) + B + 1 from by ring]
    apply stepStar_trans (ih B (by omega) (c+1) (d+2) (e+1))
    ring_nf; finish

-- Main transition: one full cycle
theorem main_trans (hE : E ≥ 2*D + 8) :
    ⟨0, 0, 0, D+1, E⟩ [fm]⊢⁺ ⟨0, 0, 0, D+2, E+D+7⟩ := by
  -- Phase 1: R4 chain
  rw [show D + 1 = 0 + (D + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (D+1) 0 (d := 0))
  simp only [Nat.zero_add]
  -- Phase 2: R5 step
  rw [show E = E - 1 + 1 from by omega]
  step fm
  -- After R5: (0, D+2, 2, 0, E-1)
  -- Phase 3: Process with B=D+2, c=1, d=0
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  rw [show E - 1 = (E - D - 4) + (D + 2) + 1 from by omega]
  apply stepStar_trans (process (D+2) 1 0 (E-D-4))
  -- Result: (0, 0, 0, 0+(D+2), (E-D-4) + 3*1 + 2*(D+2) + 4)
  -- = (0, 0, 0, D+2, E-D-4+3+2D+4+4) = (0, 0, 0, D+2, E+D+7)
  simp only [Nat.zero_add]
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 8⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D+1, E⟩ ∧ E ≥ 2*D + 8)
  · intro c ⟨D, E, hq, hE⟩; subst hq
    exact ⟨⟨0, 0, 0, D+2, E+D+7⟩, ⟨D+1, E+D+7, rfl, by omega⟩, main_trans hE⟩
  · exact ⟨0, 8, rfl, by omega⟩
