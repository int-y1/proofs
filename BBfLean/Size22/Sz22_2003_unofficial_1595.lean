import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1595: [77/15, 1/3, 6/7, 125/2, 1/55, 3/5]

Vector representation:
```
 0 -1 -1  1  1
 0 -1  0  0  0
 1  1  0 -1  0
-1  0  3  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1595

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: (a+k, 0, c, 0, e) →* (a, 0, c+3*k, 0, e)
theorem r4_chain : ∀ k, ∀ a c, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c; exists 0
  · intro a c
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    rw [show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring]
    exact ih a (c + 3)

-- R5 drain: (0, 0, c+k, 0, k) →* (0, 0, c, 0, 0)
theorem r5_drain : ∀ k, ∀ c, ⟨0, 0, c + k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih
  · intro c; exists 0
  · intro c
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    exact ih c

-- R6+R1 opening: (0, 0, c+2, 0, 0) →* (0, 0, c, 1, 1)
theorem r6_r1 : ⟨0, 0, c + 2, 0, 0⟩ [fm]⊢* ⟨0, 0, c, 1, 1⟩ := by
  step fm; step fm; finish

-- R3+R1 spiral: (a, 0, k, 1, e) →* (a+k, 0, 0, 1, e+k)
theorem r3r1_spiral : ∀ k, ∀ a e, ⟨a, 0, k, 1, e⟩ [fm]⊢* ⟨a + k, 0, 0, 1, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a e; exists 0
  · intro a e
    step fm; step fm
    rw [show a + (k + 1) = (a + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    exact ih (a + 1) (e + 1)

-- Final R3+R2: (n, 0, 0, 1, n+1) →⁺ (n+1, 0, 0, 0, n+1)
theorem final_r3r2 : ⟨n, 0, 0, 1, n + 1⟩ [fm]⊢⁺ ⟨n + 1, 0, 0, 0, n + 1⟩ := by
  step fm; step fm; finish

-- Main transition: (n+2, 0, 0, 0, n+2) →⁺ (2n+3, 0, 0, 0, 2n+3)
theorem main_trans : ⟨n + 2, 0, 0, 0, n + 2⟩ [fm]⊢⁺ ⟨2 * n + 3, 0, 0, 0, 2 * n + 3⟩ := by
  -- Phase 1: R4 chain (n+2 steps)
  have h1 : ⟨0 + (n + 2), 0, 0, 0, n + 2⟩ [fm]⊢* ⟨0, 0, 0 + 3 * (n + 2), 0, n + 2⟩ :=
    r4_chain (n + 2) 0 0
  rw [show (0 : ℕ) + (n + 2) = n + 2 from by ring,
      show (0 : ℕ) + 3 * (n + 2) = 3 * n + 6 from by ring] at h1
  -- Phase 2: R5 drain (n+2 steps)
  have h2 : ⟨0, 0, (2 * n + 4) + (n + 2), 0, n + 2⟩ [fm]⊢* ⟨0, 0, 2 * n + 4, 0, 0⟩ :=
    r5_drain (n + 2) (2 * n + 4)
  rw [show (2 * n + 4) + (n + 2) = 3 * n + 6 from by ring] at h2
  -- Phase 3: R6+R1 opening
  have h3 : ⟨0, 0, (2 * n + 2) + 2, 0, 0⟩ [fm]⊢* ⟨0, 0, 2 * n + 2, 1, 1⟩ := r6_r1
  rw [show (2 * n + 2) + 2 = 2 * n + 4 from by ring] at h3
  -- Phase 4: R3+R1 spiral (2n+2 rounds)
  have h4 : ⟨0, 0, 2 * n + 2, 1, 1⟩ [fm]⊢* ⟨0 + (2 * n + 2), 0, 0, 1, 1 + (2 * n + 2)⟩ :=
    r3r1_spiral (2 * n + 2) 0 1
  rw [show (0 : ℕ) + (2 * n + 2) = 2 * n + 2 from by ring,
      show (1 : ℕ) + (2 * n + 2) = 2 * n + 3 from by ring] at h4
  -- Phase 5: Final R3+R2
  have h5 : ⟨2 * n + 2, 0, 0, 1, 2 * n + 3⟩ [fm]⊢⁺ ⟨2 * n + 3, 0, 0, 0, 2 * n + 3⟩ :=
    final_r3r2
  exact stepStar_stepPlus_stepPlus
    (stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4))) h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, n + 2⟩) 0
  intro n; exact ⟨2 * n + 1, main_trans⟩
