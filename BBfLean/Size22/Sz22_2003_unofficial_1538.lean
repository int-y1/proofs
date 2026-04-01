import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1538: [7/30, 27/77, 22/3, 5/11, 9/2]

Vector representation:
```
-1 -1 -1  1  0
 0  3  0 -1 -1
 1 -1  0  0  1
 0  0  1  0 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1538

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R2-R3 chain: (a, b, 0, n, 1) →* (a+n, b+2n, 0, 0, 1) when c=0.
theorem r2r3_chain : ∀ n, ∀ a b, ⟨a, b, 0, n, 1⟩ [fm]⊢* ⟨a + n, b + 2 * n, 0, 0, 1⟩ := by
  intro n; induction' n with n ih <;> intro a b
  · exists 0
  · rw [show (n + 1 : ℕ) = n + 1 from rfl]
    step fm  -- R2: (a, b+3, 0, n, 0)
    step fm  -- R3: (a+1, b+2, 0, n, 1)
    apply stepStar_trans (ih (a + 1) (b + 2))
    ring_nf; finish

-- R3 drain: (a, k, 0, 0, e) →* (a+k, 0, 0, 0, e+k) when c=0, d=0.
theorem r3_drain : ∀ k, ∀ a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- R4 chain: (a, 0, c, 0, k) →* (a, 0, c+k, 0, 0) when b=0, d=0.
theorem r4_chain : ∀ k, ∀ a c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

-- R5-R1-R1 chain: (a+3k, 0, c+2k, d, 0) →* (a, 0, c, d+2k, 0).
theorem r5r1r1_chain : ∀ k, ∀ a c d, ⟨a + 3 * k, 0, c + 2 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + 3 * (k + 1) = (a + 3 * k) + 1 + 1 + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
    step fm  -- R5
    step fm  -- R1
    step fm  -- R1
    apply stepStar_trans (ih a c (d + 2))
    ring_nf; finish

-- Endgame: (2, 0, 2, D+1, 0) →⁺ (1, 4, 0, D+1, 0).
theorem endgame : ⟨2, 0, 2, D + 1, 0⟩ [fm]⊢⁺ ⟨1, 4, 0, D + 1, 0⟩ := by
  step fm  -- R5: (1, 2, 2, D+1, 0)
  step fm  -- R1: (0, 1, 1, D+2, 0)
  step fm  -- R3: (1, 0, 1, D+2, 1)
  rw [show D + 2 = (D + 1) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl]
  step fm  -- R2: (1, 3, 1, D+1, 0)
  step fm  -- R1: (0, 2, 0, D+2, 0)
  step fm  -- R3: (1, 1, 0, D+2, 1)
  rw [show D + 1 + 1 = (D + 1) + 1 from by ring, show (1 : ℕ) = 0 + 1 from rfl]
  step fm  -- R2: (1, 4, 0, D+1, 0)
  finish

-- Main transition: (1, 4, 0, 2d, 0) ⊢⁺ (1, 4, 0, 4d+2, 0).
theorem main_trans (d : ℕ) :
    ⟨1, 4, 0, 2 * d, 0⟩ [fm]⊢⁺ ⟨1, 4, 0, 4 * d + 2, 0⟩ := by
  -- Phase 1: R3 step (symbolic d, so use simp [fm])
  apply step_stepStar_stepPlus
  · show fm ⟨1, 3 + 1, 0, 2 * d, 0⟩ = some ⟨2, 3, 0, 2 * d, 1⟩; simp [fm]
  -- State: (2, 3, 0, 2d, 1)
  -- Phase 2: R2-R3 chain draining d
  apply stepStar_trans (r2r3_chain (2 * d) 2 3)
  rw [show 2 + 2 * d = 2 * d + 2 from by ring,
      show 3 + 2 * (2 * d) = 4 * d + 3 from by ring]
  -- State: (2d+2, 4d+3, 0, 0, 1)
  -- Phase 3: R3 drain
  apply stepStar_trans (r3_drain (4 * d + 3) (2 * d + 2) 1)
  rw [show 2 * d + 2 + (4 * d + 3) = 6 * d + 5 from by ring,
      show 1 + (4 * d + 3) = 4 * d + 4 from by ring]
  -- State: (6d+5, 0, 0, 0, 4d+4)
  -- Phase 4: R4 chain
  apply stepStar_trans (r4_chain (4 * d + 4) (6 * d + 5) 0)
  rw [show 0 + (4 * d + 4) = 4 * d + 4 from by ring]
  -- State: (6d+5, 0, 4d+4, 0, 0)
  -- Phase 5: R5-R1-R1 chain with k=2d+1
  rw [show 6 * d + 5 = 2 + 3 * (2 * d + 1) from by ring,
      show 4 * d + 4 = 2 + 2 * (2 * d + 1) from by ring]
  apply stepStar_trans (r5r1r1_chain (2 * d + 1) 2 2 0)
  rw [show 0 + 2 * (2 * d + 1) = 4 * d + 2 from by ring]
  -- State: (2, 0, 2, 4d+2, 0)
  -- Phase 6: Endgame
  rw [show 4 * d + 2 = (4 * d + 1) + 1 from by ring]
  exact stepPlus_stepStar endgame

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 4, 0, 0, 0⟩)
  · execute fm 12
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨1, 4, 0, 2 * d, 0⟩) 0
  intro d
  refine ⟨2 * d + 1, ?_⟩
  rw [show 2 * (2 * d + 1) = 4 * d + 2 from by ring]
  exact main_trans d

end Sz22_2003_unofficial_1538
