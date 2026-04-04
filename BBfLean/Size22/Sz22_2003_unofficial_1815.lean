import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1815: [9/10, 55/21, 2/3, 7/11, 99/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1815

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- R4 chain: move e to d. (a, 0, 0, d, k) →* (a, 0, 0, d+k, 0)
theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- R3 chain: move b to a. (a, k, 0, 0, e) →* (a+k, 0, 0, 0, e)
theorem b_to_a : ∀ k a, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1))
    ring_nf; finish

-- R2+R1 interleaved chain. (k, b+1, 0, k, e) →* (0, b+k+1, 0, 0, e+k)
theorem r2r1_chain : ∀ k b e, ⟨k, b + 1, 0, k, e⟩ [fm]⊢* ⟨0, b + k + 1, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm  -- R2
    step fm  -- R1
    apply stepStar_trans (ih (b + 1) (e + 1))
    ring_nf; finish

-- Main transition: (n+2, 0, 0, 0, n+1) →⁺ (n+3, 0, 0, 0, n+2)
theorem main_trans : ⟨n + 2, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, n + 2⟩ := by
  -- Phase 1: R4 chain: (n+2, 0, 0, 0, n+1) →* (n+2, 0, 0, n+1, 0)
  apply stepStar_stepPlus_stepPlus (e_to_d (n + 1) 0 (a := n + 2))
  rw [show 0 + (n + 1) = n + 1 from by ring]
  -- Phase 2: R5 step: (n+2, 0, 0, n+1, 0) → (n+1, 2, 0, n+1, 1)
  apply step_stepStar_stepPlus
  · show fm ⟨(n + 1) + 1, 0, 0, n + 1, 0⟩ = some ⟨n + 1, 2, 0, n + 1, 1⟩
    rw [show n + 2 = (n + 1) + 1 from by ring]; simp [fm]
  -- Phase 3: R2+R1 chain (n+1 rounds)
  show ⟨n + 1, 1 + 1, 0, n + 1, 1⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, n + 2⟩
  apply stepStar_trans (r2r1_chain (n + 1) 1 1)
  -- Now at (0, 1+(n+1)+1, 0, 0, 1+(n+1)) = (0, n+3, 0, 0, n+2)
  -- Phase 4: R3 chain: (0, n+3, 0, 0, n+2) →* (n+3, 0, 0, 0, n+2)
  show ⟨0, 1 + (n + 1) + 1, 0, 0, 1 + (n + 1)⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, n + 2⟩
  rw [show 1 + (n + 1) + 1 = n + 3 from by ring,
      show 1 + (n + 1) = n + 2 from by ring]
  apply stepStar_trans (b_to_a (n + 3) 0 (e := n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, n + 1⟩) 0
  intro n; exists n + 1; exact main_trans
