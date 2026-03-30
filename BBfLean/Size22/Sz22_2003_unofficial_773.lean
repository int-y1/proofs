import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #773: [35/6, 55/2, 16/77, 3/5, 7/3]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  1
 4  0  0 -1 -1
 0  1 -1  0  0
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_773

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+4, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: move c to b (when a=0, d=0).
theorem c_to_b : ∀ k, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring]
    step fm
    exact ih

-- R3/R2 interleaving (b=0, a=0): each cycle is R3 then R2 x4.
theorem r3r2_chain : ∀ k, ⟨0, 0, c, k, e + 1⟩ [fm]⊢* ⟨0, 0, c + 4 * k, 0, e + 3 * k + 1⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [show c + 4 * (k + 1) = (c + 4) + 4 * k from by ring,
        show e + 3 * (k + 1) + 1 = (e + 3) + 3 * k + 1 from by ring]
    step fm -- R3: (4, 0, c, k, e)
    step fm -- R2: (3, 0, c+1, k, e+1)
    step fm -- R2: (2, 0, c+2, k, e+2)
    step fm -- R2: (1, 0, c+3, k, e+3)
    step fm -- R2: (0, 0, c+4, k, e+4)
    exact ih

-- Big cycle: R1 x4 then R3.
theorem big_cycle : ⟨4, b + 4, c, d, e + 1⟩ [fm]⊢* ⟨4, b, c + 4, d + 3, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Full spiral by strong induction on B.
theorem full_spiral : ∀ B, ∀ c d E, E ≥ B / 4 →
    ⟨4, B, c, d, E⟩ [fm]⊢* ⟨0, 0, c + 4 * (B + d + 1), 0, E + 2 * B + 3 * d + 4⟩ := by
  intro B
  induction' B using Nat.strongRecOn with B IH
  intro c d E hE
  rcases B with _ | _ | _ | _ | B
  · -- B = 0
    step fm; step fm; step fm; step fm
    rw [show c + 4 * (0 + d + 1) = (c + 4) + 4 * d from by ring,
        show E + 2 * 0 + 3 * d + 4 = (E + 3) + 3 * d + 1 from by ring]
    exact r3r2_chain d
  · -- B = 1
    step fm; step fm; step fm; step fm
    rw [show c + 4 * (1 + d + 1) = (c + 4) + 4 * (d + 1) from by ring,
        show E + 2 * 1 + 3 * d + 4 = (E + 2) + 3 * (d + 1) + 1 from by ring]
    exact r3r2_chain (d + 1)
  · -- B = 2
    step fm; step fm; step fm; step fm
    rw [show c + 4 * (2 + d + 1) = (c + 4) + 4 * (d + 2) from by ring,
        show E + 2 * 2 + 3 * d + 4 = (E + 1) + 3 * (d + 2) + 1 from by ring]
    exact r3r2_chain (d + 2)
  · -- B = 3
    step fm; step fm; step fm; step fm
    rw [show c + 4 * (3 + d + 1) = (c + 4) + 4 * (d + 3) from by ring,
        show E + 2 * 3 + 3 * d + 4 = E + 3 * (d + 3) + 1 from by ring]
    exact r3r2_chain (d + 3)
  · -- B + 4
    rw [show B + 1 + 1 + 1 + 1 = B + 4 from by ring]
    obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
    apply stepStar_trans (big_cycle (b := B) (c := c) (d := d) (e := E'))
    rw [show c + 4 * (B + 4 + d + 1) = (c + 4) + 4 * (B + (d + 3) + 1) from by ring,
        show E' + 1 + 2 * (B + 4) + 3 * d + 4 = E' + 2 * B + 3 * (d + 3) + 4 from by ring]
    exact IH B (by omega) (c + 4) (d + 3) E' (by omega)

-- Main transition.
theorem main_transition (C E : ℕ) (hC : C ≥ 1) (hE : 2 * E ≥ C) :
    ⟨0, 0, C, 0, E⟩ [fm]⊢⁺ ⟨0, 0, 4 * C, 0, E + 2 * C + 1⟩ := by
  obtain ⟨C', rfl⟩ : ∃ C', C = C' + 1 := ⟨C - 1, by omega⟩
  obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
  -- Phase 1: R4 chain
  apply stepStar_stepPlus_stepPlus
  · rw [show (C' + 1 : ℕ) = 0 + (C' + 1) from by ring]
    exact c_to_b (C' + 1)
  -- Phase 2: R5
  apply step_stepPlus_stepPlus
  · rw [show (0 : ℕ) + (C' + 1) = C' + 1 from by ring]; rfl
  -- Phase 3: R3
  apply step_stepStar_stepPlus
  · rfl
  -- Phase 4: Full spiral
  rw [show 4 * (C' + 1) = 0 + 4 * (C' + 0 + 1) from by ring,
      show (E' + 1) + 2 * (C' + 1) + 1 = E' + 2 * C' + 3 * 0 + 4 from by ring]
  exact full_spiral C' 0 0 E' (by omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 4⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ C E, q = ⟨0, 0, C, 0, E⟩ ∧ C ≥ 1 ∧ 2 * E ≥ C)
  · intro q ⟨C, E, hq, hC, hE⟩; subst hq
    exact ⟨⟨0, 0, 4 * C, 0, E + 2 * C + 1⟩,
      ⟨4 * C, E + 2 * C + 1, rfl, by omega, by omega⟩,
      main_transition C E hC hE⟩
  · exact ⟨4, 4, rfl, by omega, by omega⟩
