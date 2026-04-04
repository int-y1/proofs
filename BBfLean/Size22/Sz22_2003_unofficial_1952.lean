import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1952: [9/70, 605/2, 2/33, 49/11, 2/7]

Vector representation:
```
-1  2 -1 -1  0
-1  0  1  0  2
 1 -1  0  0 -1
 0  0  0  2 -1
 1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1952

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 repeated: (0, 0, c, d, e+k) →* (0, 0, c, d+2k, e)
theorem e_to_d : ∀ k d, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 2))
    ring_nf; finish

-- R5+R1 chain: (0, b, c+k, d+2*k, 0) →* (0, b+2*k, c, d, 0)
-- step fm needs d+2*k to look like succ. We write it as: for k ≥ 1, split off one round.
theorem r5r1_chain : ∀ k b c d, ⟨0, b, c + k, d + 2 * k, 0⟩ [fm]⊢* ⟨0, b + 2 * k, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring,
        show d + 2 * (k + 1) = d + 2 * k + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b + 2) c d)
    ring_nf; finish

-- Bridge: (0, b+1, 0, 2, 0) →⁺ (1, b+1, 0, 0, 0)
theorem bridge : ⟨0, b + 1, 0, 2, 0⟩ [fm]⊢⁺ ⟨1, b + 1, 0, 0, 0⟩ := by
  execute fm 5

-- R2+R3 chain: (1, b+k, c, 0, e) →* (1, b, c+k, 0, e+k)
theorem r2r3_chain : ∀ k b c e, ⟨1, b + k, c, 0, e⟩ [fm]⊢* ⟨1, b, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih b (c + 1) (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, c+1, 0, c+2) →⁺ (0, 0, 2c+3, 0, 2c+4)
theorem main_trans : ∀ c, ⟨0, 0, c + 1, 0, c + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 3, 0, 2 * c + 4⟩ := by
  intro c
  apply stepStar_stepPlus_stepPlus
  · rw [show (c : ℕ) + 2 = 0 + (c + 2) from by ring]
    have h := e_to_d (c + 2) 0 (c := c + 1) (e := 0)
    rw [show 0 + 2 * (c + 2) = 2 * c + 4 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus
  · rw [show (c : ℕ) + 1 = 0 + (c + 1) from by ring,
        show 2 * c + 4 = 2 + 2 * (c + 1) from by ring]
    have h := r5r1_chain (c + 1) 0 0 2
    rw [show 0 + 2 * (c + 1) = 2 * c + 2 from by ring] at h
    exact h
  rw [show 2 * c + 2 = (2 * c + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (bridge (b := 2 * c + 1))
  rw [show (2 * c + 1 : ℕ) + 1 = 0 + (2 * c + 2) from by ring]
  apply stepStar_trans (r2r3_chain (2 * c + 2) 0 0 0)
  simp only [Nat.zero_add]
  step fm; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, n + 1, 0, n + 2⟩) 0
  intro n; exists 2 * n + 2
  exact main_trans n
