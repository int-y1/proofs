import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #758: [35/6, 4/55, 847/2, 3/7, 5/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_758

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ c d e,
    ⟨2, 2 * (k + 1), c, d, e + k + 1⟩ [fm]⊢* ⟨0, 0, c + k + 2, d + 2 * k + 2, e + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; step fm; finish
  · rw [show 2 * (k + 1 + 1) = (2 * (k + 1) + 1) + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm
    rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 from by ring]
    step fm
    step fm
    rw [show d + 1 + 1 = d + 2 from by ring]
    have := ih (c + 1) (d + 2) e
    convert this using 2; ring_nf

-- Phase 4-8: from (n+3, 2n+4, n+2) to (4n+10, 4n+11)
theorem phases_4_8 (n : ℕ) :
    ⟨0, 0, n + 3, 2 * n + 4, n + 2⟩ [fm]⊢* ⟨0, 4 * n + 10, 0, 0, 4 * n + 11⟩ := by
  -- Phase 4: R2 chain
  have h4 := r2_chain (n + 2) 0 1 (2 * n + 4) 0
  rw [show 1 + (n + 2) = n + 3 from by ring,
      show 0 + (n + 2) = n + 2 from by ring] at h4
  apply stepStar_trans h4
  -- Phase 5: R3
  rw [show 0 + 2 * (n + 2) = (2 * n + 3) + 1 from by ring]
  step fm
  -- Phase 6: R2
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  -- Phase 7: R3 chain
  have h7 := r3_chain (2 * n + 5) 0 (2 * n + 5) 1
  rw [show 0 + (2 * n + 5) = 2 * n + 5 from by ring] at h7
  rw [show 2 * n + 3 + 2 = 2 * n + 5 from by ring,
      show 2 * n + 4 + 1 = 2 * n + 5 from by ring]
  apply stepStar_trans h7
  -- Phase 8: R4 chain
  rw [show 2 * n + 5 + (2 * n + 5) = 4 * n + 10 from by ring,
      show 1 + 2 * (2 * n + 5) = 4 * n + 11 from by ring,
      show 4 * n + 10 = 0 + (4 * n + 10) from by omega]
  have h8 := r4_chain (4 * n + 10) 0 0 (4 * n + 11)
  exact h8

-- Compose all phases: (0, 2n+4, 0, 0, 2n+5) ⊢⁺ (0, 4n+10, 0, 0, 4n+11)
theorem main_trans (n : ℕ) :
    ⟨0, 2 * n + 4, 0, 0, 2 * n + 5⟩ [fm]⊢⁺ ⟨0, 4 * n + 10, 0, 0, 4 * n + 11⟩ := by
  -- Phase 1: R5
  rw [show 2 * n + 5 = (2 * n + 4) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * n + 4, 0, 0, (2 * n + 4) + 1⟩ = some ⟨0, 2 * n + 4, 1, 0, 2 * n + 4⟩
    simp [fm]
  -- Phase 2: R2 (single step)
  rw [show 2 * n + 4 = (2 * n + 3) + 1 from by ring]
  step fm
  -- Phase 3: R1R1R2 chain
  rw [show 2 * n + 4 = 2 * ((n + 1) + 1) from by ring,
      show 2 * n + 3 = (n + 1) + (n + 1) + 1 from by ring]
  apply stepStar_trans (r1r1r2_chain (n + 1) 0 0 (n + 1))
  -- State: (0, 0, 0+(n+1)+2, 0+2*(n+1)+2, (n+1)+1)
  have key := phases_4_8 n
  have : ⟨0, 0, 0 + (n + 1) + 2, 0 + 2 * (n + 1) + 2, (n + 1) + 1⟩ =
         (⟨0, 0, n + 3, 2 * n + 4, n + 2⟩ : Q) := by ring_nf
  rw [this]
  exact key

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 4, 0, 0, 5⟩) (by execute fm 13)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2 * n + 4, 0, 0, 2 * n + 5⟩) 0
  intro n
  refine ⟨2 * n + 3, ?_⟩
  have key := main_trans n
  convert key using 2
  · ring_nf

end Sz22_2003_unofficial_758
