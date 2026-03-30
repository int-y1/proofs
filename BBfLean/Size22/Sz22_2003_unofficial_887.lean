import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #887: [4/15, 147/2, 11/3, 5/77, 3/7, 1/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  2  0
 0 -1  0  0  1
 0  0  1 -1 -1
 0  1  0 -1  0
 0  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_887

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- Phase 1: R2 chain. Consumes a, produces b and d.
-- When c=0 and e=0, R1 can't fire (needs c >= 1), so R2 fires while a >= 1.
theorem r2_chain : ∀ k b d, ⟨k, b, 0, d, 0⟩ [fm]⊢* ⟨0, b + k, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show k + 1 = (k + 1) from rfl]
    step fm
    apply stepStar_trans (ih (b + 1) (d + 2))
    ring_nf; finish

-- Phase 2: R3 chain. Consumes b, produces e.
-- When a=0 and c=0, R1 can't fire, R2 can't fire, so R3 fires while b >= 1.
theorem r3_chain : ∀ k d e, ⟨0, k, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- Phase 3: R4 chain. Consumes d and e in parallel, produces c.
-- When a=0, b=0, R1-R3 can't fire. R4 fires while d >= 1 and e >= 1.
theorem r4_chain : ∀ k c d, ⟨0, 0, c, d + k, k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- Phase 4: Interleaved R2+R1 chain. Each round: R2 then R1.
-- From (a+1, 0, k+1, d, 0): R2 fires (a+1 >= 1), then R1 fires (b=1, c >= 1).
-- Each round: a increases by 1, c decreases by 1, d increases by 2.
theorem r2r1_chain : ∀ k a d, ⟨a + 1, 0, k, d, 0⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm  -- R2: (a, 1, k+1, d+2, 0)
    step fm  -- R1: (a+2, 0, k, d+2, 0)
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (d + 2))
    ring_nf; finish

-- Phase 4 opener: R5 then R1, then R2+R1 chain.
-- From (0, 0, c+1, d+1, 0):
--   R5: (0, 1, c+1, d, 0)
--   R1: (2, 0, c, d, 0)
--   R2+R1 chain with a=1: (2+c, 0, 0, d+2*c, 0) = (c+2, 0, 0, d+2*c, 0)
theorem r5_r1_chain : ∀ c d, ⟨0, 0, c + 1, d + 1, 0⟩ [fm]⊢* ⟨c + 2, 0, 0, d + 2 * c, 0⟩ := by
  intro c d
  step fm  -- R5: (0, 1, c+1, d, 0)
  step fm  -- R1: (2, 0, c, d, 0)
  show ⟨1 + 1, 0, c, d, 0⟩ [fm]⊢* ⟨c + 2, 0, 0, d + 2 * c, 0⟩
  rw [show (1 : ℕ) + 1 = 1 + 1 from rfl]
  apply stepStar_trans (r2r1_chain c 1 d)
  ring_nf; finish

-- Compose phases 1-4 as ⊢*
theorem all_phases (a d : ℕ) : ⟨a + 2, 0, 0, d, 0⟩ [fm]⊢* ⟨a + 3, 0, 0, d + 3 * (a + 1), 0⟩ := by
  -- Phase 1: R2 chain
  apply stepStar_trans (r2_chain (a + 2) 0 d)
  -- Phase 2: R3 chain
  apply stepStar_trans
  · rw [show (0 : ℕ) + (a + 2) = a + 2 from by ring]
    exact r3_chain (a + 2) (d + 2 * (a + 2)) 0
  -- Phase 3: R4 chain
  apply stepStar_trans
  · rw [show (0 : ℕ) + (a + 2) = a + 2 from by ring,
        show d + 2 * (a + 2) = (d + a + 2) + (a + 2) from by ring]
    exact r4_chain (a + 2) 0 (d + a + 2)
  -- Phase 4: R5+R1+(R2+R1) chain
  show ⟨0, 0, 0 + (a + 2), d + a + 2, 0⟩ [fm]⊢* _
  rw [show (0 : ℕ) + (a + 2) = (a + 1) + 1 from by ring,
      show d + a + 2 = (d + a + 1) + 1 from by ring]
  apply stepStar_trans (r5_r1_chain (a + 1) (d + a + 1))
  ring_nf; finish

-- Main transition: (a+2, 0, 0, d, 0) ⊢⁺ (a+3, 0, 0, d + 3*(a+1), 0)
theorem main_trans (a d : ℕ) : ⟨a + 2, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, d + 3 * (a + 1), 0⟩ := by
  apply stepStar_stepPlus (all_phases a d)
  simp [Q]

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 2, 0, 0, d, 0⟩) ⟨0, 0⟩
  intro ⟨a, d⟩; exact ⟨⟨a + 1, d + 3 * (a + 1)⟩, main_trans a d⟩

end Sz22_2003_unofficial_887
