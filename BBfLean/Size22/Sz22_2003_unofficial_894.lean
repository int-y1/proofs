import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #894: [4/15, 147/22, 25/2, 11/7, 22/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  2 -1
-1  0  2  0  0
 0  0  0 -1  1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_894

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R3 chain: (k, 0, c, d, 0) →* (0, 0, c+2*k, d, 0).
theorem r3_chain : ∀ k c, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 2))
    ring_nf; finish

-- R4 chain: (0, 0, c, k, e) →* (0, 0, c, 0, e+k).
theorem r4_chain : ∀ k e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  · step fm
    apply stepStar_trans (ih (e + 1))
    ring_nf; finish

-- R2/R1 spiral: (a+1, 0, n, d, n) →* (a+n+1, 0, 0, d+2*n, 0).
theorem spiral : ∀ n, ∀ a d, ⟨a + 1, 0, n, d, n⟩ [fm]⊢* ⟨a + n + 1, 0, 0, d + 2 * n, 0⟩ := by
  intro n; induction' n with n ih <;> intro a d
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (a + 1) (d + 2))
    ring_nf; finish

-- Main transition: (a+2, 0, 0, 2*a+2, 0) →⁺ (2*a+4, 0, 0, 4*a+6, 0).
theorem main_transition (a : ℕ) :
    ⟨a + 2, 0, 0, 2 * a + 2, 0⟩ [fm]⊢⁺ ⟨2 * a + 4, 0, 0, 4 * a + 6, 0⟩ := by
  -- R3 first step to get ⊢⁺
  rw [show a + 2 = (a + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (r3_chain (a + 1) 2 (d := 2 * a + 2))
  rw [show 2 + 2 * (a + 1) = 2 * a + 4 from by ring]
  -- R4 chain: (0, 0, 2a+4, 2a+2, 0) →* (0, 0, 2a+4, 0, 2a+2)
  apply stepStar_trans (r4_chain (2 * a + 2) 0 (c := 2 * a + 4))
  rw [show 0 + (2 * a + 2) = 2 * a + 2 from by ring]
  -- R5 step: (0, 0, 2a+4, 0, 2a+2) → (1, 0, 2a+3, 0, 2a+3)
  rw [show (2 * a + 4 : ℕ) = (2 * a + 3) + 1 from by ring]
  step fm
  rw [show (2 * a + 2 + 1 : ℕ) = 2 * a + 3 from by ring]
  -- Spiral (2a+3 rounds): (1, 0, 2a+3, 0, 2a+3) →* (2a+4, 0, 0, 4a+6, 0)
  apply stepStar_trans (spiral (2 * a + 3) 0 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun a ↦ ⟨a + 2, 0, 0, 2 * a + 2, 0⟩) 0
  intro a
  refine ⟨2 * a + 2, ?_⟩
  rw [show 2 * a + 2 + 2 = 2 * a + 4 from by ring,
      show 2 * (2 * a + 2) + 2 = 4 * a + 6 from by ring]
  exact main_transition a
