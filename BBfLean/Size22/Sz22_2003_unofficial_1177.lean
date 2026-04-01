import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1177: [5/6, 49/2, 44/35, 3/11, 242/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  1  0  0 -1
 1  0  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1177

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R4 chain: move e to b.
theorem e_to_b : ∀ k b, ⟨(0 : ℕ), b, 0, d, k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

-- R3+R2+R2 drain chain.
theorem drain : ∀ k, ⟨(0 : ℕ), 0, k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, d + 3 * k + 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · step fm; step fm; step fm
    rw [show d + 3 + 1 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 3) (e := e + 1))
    ring_nf; finish

-- Interleaved R1+R1+R3 chain then final R1.
-- From (2, 2k+1, c, D+k, E) →* (1, 0, c+k+1, D, E+k)
theorem interleaved : ∀ k c D E, ⟨(2 : ℕ), 2 * k + 1, c, D + k, E⟩ [fm]⊢*
    ⟨(1 : ℕ), 0, c + k + 1, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro c D E
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring,
        show D + (k + 1) = (D + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) D (E + 1))
    ring_nf; finish

-- Combined: from after R5 to the end.
-- (1, 2*(n+1), 0, (n+1)^2+1, 2) →* (0, 0, 0, (n+2)^2+2, 2*(n+2))
theorem middle_to_end (n : ℕ) :
    ⟨(1 : ℕ), 2 * (n + 1), 0, (n + 1) * (n + 1) + 1, 2⟩ [fm]⊢*
    ⟨(0 : ℕ), 0, 0, (n + 2) * (n + 2) + 2, 2 * (n + 2)⟩ := by
  -- R1
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
  step fm
  -- R3
  rw [show (n + 1) * (n + 1) + 1 = (n * n + 2 * n + 1) + 1 from by ring]
  step fm
  -- interleaved
  rw [show n * n + 2 * n + 1 = (n * n + n + 1) + n from by ring]
  apply stepStar_trans (interleaved n (c := 0) (D := n * n + n + 1) (E := 3))
  rw [show (0 : ℕ) + n + 1 = n + 1 from by ring,
      show (3 : ℕ) + n = n + 3 from by ring]
  -- R2
  step fm
  -- drain
  rw [show n * n + n + 1 + 2 = (n * n + n + 2) + 1 from by ring]
  apply stepStar_trans (drain (n + 1) (d := n * n + n + 2) (e := n + 3))
  ring_nf; finish

-- Main transition for n ≥ 0.
theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, (n + 1) * (n + 1) + 2, 2 * (n + 1)⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, (n + 2) * (n + 2) + 2, 2 * (n + 2)⟩ := by
  -- Phase 1: e_to_b
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * (n + 1)) 0 (d := (n + 1) * (n + 1) + 2))
  -- Phase 2: R5 (gives the stepPlus)
  rw [show (n + 1) * (n + 1) + 2 = (n + 1) * (n + 1) + 1 + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Now need stepStar from (1, 2*(n+1), 0, (n+1)^2+1, 2) to target
  simp only [Nat.zero_add]
  exact middle_to_end n

-- Base case: (0, 0, 0, 2, 0) →⁺ (0, 0, 0, 3, 2)
theorem base_trans : ⟨(0 : ℕ), 0, 0, 2, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 3, 2⟩ := by
  execute fm 2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n * n + 2, 2 * n⟩) 0
  intro n
  rcases n with _ | n
  · exact ⟨1, base_trans⟩
  · exact ⟨n + 2, main_trans n⟩
