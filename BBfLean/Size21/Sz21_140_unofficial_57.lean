import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #57: [35/6, 8/55, 77/2, 3/7, 5/3]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  1  1
 0  1  0 -1  0
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_57

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 repeated: (a+k, 0, 0, d, e) →* (a, 0, 0, d+k, e+k)
-- R3 fires because b=0, c=0, and a+k ≥ 1
theorem r3_repeat : ∀ k, ∀ a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+k, e+k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 repeated: (0, b, 0, d+k, e) →* (0, b+k, 0, d, e)
theorem r4_repeat : ∀ k, ∀ b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- One cycle of R1×3 + R2: (3, b+3, c, d, e+1) →⁺ (3, b, c+2, d+3, e)
theorem r1x3_r2_one : ⟨3, b+3, c, d, e+1⟩ [fm]⊢⁺ ⟨3, b, c+2, d+3, e⟩ := by
  rw [show b + 3 = (b + 2) + 1 from by ring]
  step fm
  rw [show b + 2 = (b + 1) + 1 from by ring]
  step fm
  rw [show (b + 1 : ℕ) = b + 1 from rfl]
  step fm
  step fm
  finish

-- k cycles of R1×3 + R2: (3, b+3*k, c, d, e+k) →* (3, b, c+2*k, d+3*k, e)
theorem r1x3_r2_cycles : ∀ k, ∀ c d e, ⟨3, b+3*k, c, d, e+k⟩ [fm]⊢* ⟨3, b, c+2*k, d+3*k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar r1x3_r2_one)
  have h1 := h (c + 2) (d + 3) e
  rw [show (c + 2) + 2 * k = c + 2 * (k + 1) from by ring,
      show (d + 3) + 3 * k = d + 3 * (k + 1) from by ring] at h1
  exact h1

-- R2 repeated: (a, 0, c+k, d, k) →* (a+3*k, 0, c, d, 0)
theorem r2_repeat : ∀ k, ∀ a c, ⟨a, 0, c+k, d, k⟩ [fm]⊢* ⟨a+3*k, 0, c, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3+R2 alternating: (a+1, 0, k, d, 0) →* (a+1+2*k, 0, 0, d+k, 0)
-- Each pair: R3 gives (a, 0, k, d+1, 1), then R2 gives (a+3, 0, k-1, d+1, 0).
-- Net per pair: a increases by 2, c decreases by 1, d increases by 1.
theorem r3_r2_repeat : ∀ k, ∀ a d, ⟨a+1, 0, k, d, 0⟩ [fm]⊢* ⟨a+1+2*k, 0, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  -- State: (a+1, 0, k+1, d, 0). R3 fires: (a, 0, k+1, d+1, 1).
  -- Then R2 fires (c=k+1 ≥ 1, e=1 ≥ 1): (a+3, 0, k, d+1, 0).
  -- Now apply IH with a' = a+2, d' = d+1: (a+2+1, 0, k, d+1, 0) →* (a+2+1+2*k, 0, 0, d+1+k, 0)
  step fm
  rw [show k + 1 = k + 1 from rfl]
  step fm
  have h1 := h (a + 2) (d + 1)
  rw [show a + 2 + 1 = a + 3 from by ring] at h1
  refine stepStar_trans h1 ?_
  ring_nf; finish

-- Main transition: for m ≥ 2, j + 2 ≤ 2*m:
-- (m+1+j, 0, 0, 2*m-1-j, 0) ⊢⁺ (4*m+j+2, 0, 0, 5*m-j-2, 0)
theorem main_trans (m j : ℕ) (hm : m ≥ 2) (hj : j + 2 ≤ 2 * m) :
    ⟨m + 1 + j, 0, 0, 2*m - 1 - j, 0⟩ [fm]⊢⁺
    ⟨4*m + j + 2, 0, 0, 5*m - j - 2, 0⟩ := by
  -- Phase 1: R3 × (m+1+j): →* (0, 0, 0, 3*m, m+1+j)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 3*m, m+1+j⟩)
  · have h1 := r3_repeat (m+1+j) 0 (2*m-1-j) 0
    rw [Nat.zero_add, show 2 * m - 1 - j + (m + 1 + j) = 3 * m from by omega] at h1
    simpa using h1
  -- Phase 2: R4 × (3*m): →* (0, 3*m, 0, 0, m+1+j)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3*m, 0, 0, m+1+j⟩)
  · have h2 := r4_repeat (e := m+1+j) (3*m) 0 0
    simp only [Nat.zero_add] at h2; exact h2
  -- Phase 3: R5 then R2: →⁺ (3, 3*m-1, 0, 0, m+j)
  apply stepPlus_stepStar_stepPlus (c₂ := ⟨3, 3*m-1, 0, 0, m+j⟩)
  · rw [show 3 * m = (3 * m - 1) + 1 from by omega,
        show m + 1 + j = (m + j) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 4: (m-1) cycles of R1×3+R2: →* (3, 2, 2*(m-1), 3*(m-1), j+1)
  apply stepStar_trans (c₂ := ⟨3, 2, 2*(m-1), 3*(m-1), j+1⟩)
  · have h4 := r1x3_r2_cycles (b := 2) (m - 1) 0 0 (j + 1)
    rw [Nat.zero_add, Nat.zero_add,
        show 2 + 3 * (m - 1) = 3 * m - 1 from by omega,
        show j + 1 + (m - 1) = m + j from by omega] at h4
    exact h4
  -- Phase 5: R1 × 2: →* (1, 0, 2*m, 3*m-1, j+1)
  apply stepStar_trans (c₂ := ⟨1, 0, 2*m, 3*m-1, j+1⟩)
  · rw [show (2 : ℕ) = 1 + 1 from rfl]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show 2 * (m - 1) + 1 + 1 = 2 * m from by omega,
        show 3 * (m - 1) + 1 + 1 = 3 * m - 1 from by omega]
    finish
  -- Phase 6: R2 × (j+1): →* (3*j+4, 0, 2*m-j-1, 3*m-1, 0)
  apply stepStar_trans (c₂ := ⟨3*j+4, 0, 2*m-j-1, 3*m-1, 0⟩)
  · have h6 := r2_repeat (d := 3*m-1) (j + 1) 1 (2*m - j - 1)
    rw [show 2 * m - j - 1 + (j + 1) = 2 * m from by omega,
        show 1 + 3 * (j + 1) = 3 * j + 4 from by ring] at h6
    exact h6
  -- Phase 7: R3+R2 × (2*m-j-1): →* (4*m+j+2, 0, 0, 5*m-j-2, 0)
  -- r3_r2_repeat: (A+1, 0, K, D, 0) →* (A+1+2*K, 0, 0, D+K, 0)
  -- A = 3*j+3, K = 2*m-j-1, D = 3*m-1
  have h7 := r3_r2_repeat (2*m - j - 1) (3*j + 3) (3*m - 1)
  rw [show 3 * j + 3 + 1 = 3 * j + 4 from by ring,
      show 3 * j + 3 + 1 + 2 * (2 * m - j - 1) = 4 * m + j + 2 from by omega,
      show 3 * m - 1 + (2 * m - j - 1) = 5 * m - j - 2 from by omega] at h7
  exact h7

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 2, 0⟩) (by execute fm 16)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m j, q = ⟨m + 1 + j, 0, 0, 2*m - 1 - j, 0⟩ ∧ m ≥ 2 ∧ j + 2 ≤ 2 * m)
  · intro q ⟨m, j, hq, hm, hj⟩
    refine ⟨⟨4*m + j + 2, 0, 0, 5*m - j - 2, 0⟩, ?_, ?_⟩
    · refine ⟨3*m, m + j + 1, ?_, by omega, by omega⟩
      show (4*m+j+2, 0, 0, 5*m-j-2, 0) = (3*m+1+(m+j+1), 0, 0, 2*(3*m)-1-(m+j+1), 0)
      have h1 : 4*m+j+2 = 3*m+1+(m+j+1) := by omega
      have h2 : 5*m-j-2 = 2*(3*m)-1-(m+j+1) := by omega
      rw [h1, h2]
    · subst hq; exact main_trans m j hm hj
  · exact ⟨3, 3, rfl, by omega, by omega⟩
