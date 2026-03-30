import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #798: [35/6, 605/2, 4/77, 3/5, 49/3]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 0 -1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_798

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | _ => none

-- Phase 1: R4 chain. Move c to b.
-- (0, b, c+k, 0, e) →* (0, b+k, c, 0, e)
theorem c_to_b : ∀ k b, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

-- Phase 3: R3/R2 chain.
-- (0, 0, c, k, e+1) →* (0, 0, c+2*k, 0, e+3*k+1)
theorem r3r2_chain : ∀ k c e, ⟨0, 0, c, k, e + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + 3 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + (0 + 1) from by ring,
        show e + 1 = e + (0 + 1) from by ring]
    step fm  -- R3
    step fm  -- R2
    step fm  -- R2
    apply stepStar_trans (ih (c + 2) (e + 3))
    ring_nf; finish

-- Interleave core: R1/R1/R3 chain.
-- (2, 2*k+1, c, d+1, e+k) →* (0, 0, c+2*(k+1), d+k+2, e+2)
theorem interleave_core : ∀ k c d, ⟨2, 2 * k + 1, c, d + 1, e + k⟩ [fm]⊢*
    ⟨0, 0, c + 2 * (k + 1), d + k + 2, e + 2⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · -- k=0: (2, 1, c, d+1, e) → R1 → (1, 0, c+1, d+2, e) → R2 → (0, 0, c+2, d+2, e+2)
    step fm  -- R1
    step fm  -- R2
    ring_nf; finish
  · -- k+1: (2, 2k+3, c, d+1, e+k+1)
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm  -- R1
    step fm  -- R1
    rw [show d + 1 + 1 + 1 = (d + 1) + 1 + 1 from by ring,
        show e + k + 1 = (e + k) + (0 + 1) from by ring]
    step fm  -- R3
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 2) (d + 1))
    ring_nf; finish

-- Full transition for even c.
-- From (0, 0, 2*(k+1), 0, e+k+1):
--   Phase 1: →* (0, 2*(k+1), 0, 0, e+k+1)
--   R5: → (0, 2k+1, 0, 2, e+k+1)
--   R3: → (2, 2k+1, 0, 1, e+k)
--   Interleave: →* (0, 0, 2*(k+1), k+2, e+2)
--   Phase 3: →* (0, 0, 4k+6, 0, e+3k+8)
theorem phase1_r5_r3 : ⟨0, 0, 2 * (k + 1), 0, e + k + 1⟩ [fm]⊢*
    ⟨2, 2 * k + 1, 0, 1, e + k⟩ := by
  -- Phase 1: c_to_b
  rw [show (2 * (k + 1) : ℕ) = 0 + 2 * (k + 1) from by ring]
  apply stepStar_trans (c_to_b (2 * (k + 1)) 0)
  -- R5
  rw [show 0 + 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
  step fm  -- R5
  -- R3
  rw [show e + k + 1 = (e + k) + (0 + 1) from by ring]
  step fm  -- R3
  finish

theorem phase3_close : ⟨0, 0, 2 * k + 2, k + 2, e + 2⟩ [fm]⊢⁺
    ⟨0, 0, 4 * k + 6, 0, e + 3 * k + 8⟩ := by
  rw [show e + 2 = (e + 1) + 1 from by ring]
  -- Take one R3/R2 step to make it ⊢⁺
  step fm  -- R3
  step fm  -- R2
  step fm  -- R2
  -- Now apply r3r2_chain for remaining k+1 steps
  rw [show (k + 1 : ℕ) = k + (0 + 1) from by ring,
      show e + 1 + 4 = (e + 4) + (0 + 1) from by ring]
  apply stepStar_trans (r3r2_chain (k + 1) (2 * k + 4) (e + 4))
  ring_nf; finish

theorem full_trans : ⟨0, 0, 2 * (k + 1), 0, e + k + 1⟩ [fm]⊢⁺
    ⟨0, 0, 4 * k + 6, 0, e + 3 * k + 8⟩ := by
  apply stepStar_stepPlus_stepPlus phase1_r5_r3
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (interleave_core k 0 0)
  rw [show 0 + k + 2 = k + 2 from by ring,
      show 0 + 2 * (k + 1) = 2 * k + 2 from by ring]
  exact phase3_close

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 8⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, m⟩ ↦ ⟨0, 0, 2 * n + 4, 0, n + m + 8⟩) ⟨0, 0⟩
  intro ⟨n, m⟩
  exists ⟨2 * n + 3, n + m + 6⟩
  show ⟨0, 0, 2 * n + 4, 0, n + m + 8⟩ [fm]⊢⁺ ⟨0, 0, 2 * (2 * n + 3) + 4, 0, 2 * n + 3 + (n + m + 6) + 8⟩
  rw [show 2 * n + 4 = 2 * (n + 1 + 1) from by ring,
      show n + m + 8 = (m + 6) + (n + 1) + 1 from by ring,
      show 2 * (2 * n + 3) + 4 = 4 * (n + 1) + 6 from by ring,
      show 2 * n + 3 + (n + m + 6) + 8 = (m + 6) + 3 * (n + 1) + 8 from by ring]
  exact full_trans

end Sz22_2003_unofficial_798
