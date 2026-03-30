import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #782: [35/6, 55/2, 8/77, 3/5, 7/3]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  1
 3  0  0 -1 -1
 0  1 -1  0  0
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_782

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: move c to b. Uses c >= 1 at each step.
theorem c_to_b : ∀ k b c, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c)
    ring_nf; finish

-- R1+R3 interleaving: 3 R1 steps then 1 R3. Runs k rounds.
-- Input:  (3, 3k+2, c, d, e+k)
-- Output: (3, 2, c+3k, d+2k, e)
theorem r1r3_loop : ∀ k c d e, ⟨3, 3 * k + 2, c, d, e + k⟩ [fm]⊢*
    ⟨3, 2, c + 3 * k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show c + 1 + 1 + 1 = c + 3 from by ring]
    apply stepStar_trans (ih (c + 3) (d + 2) e)
    ring_nf; finish

-- R3 + 3*R2 repeated: each round c+=3, d-=1, e+=2.
-- Input:  (0, 0, c, d+k, e+1)
-- Output: (0, 0, c+3k, d, e+2k+1)
theorem r3r2_loop : ∀ k c d e, ⟨0, 0, c, d + k, e + 1⟩ [fm]⊢*
    ⟨0, 0, c + 3 * k, d, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show c + 1 + 1 + 1 = c + 3 from by ring,
        show e + 1 + 1 + 1 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih (c + 3) d (e + 2))
    ring_nf; finish

-- Full transition: (0, 0, 3*(m+1), 0, e+m+1) →⁺ (0, 0, 9*(m+1), 0, e+4*m+5)
theorem main_trans (m e : ℕ) : ⟨0, 0, 3 * (m + 1), 0, e + m + 1⟩ [fm]⊢⁺
    ⟨0, 0, 9 * (m + 1), 0, e + 4 * m + 5⟩ := by
  -- Phase 1: c_to_b: (0, 0, 3m+3, 0, e+m+1) →* (0, 3m+3, 0, 0, e+m+1)
  rw [show 3 * (m + 1) = 0 + (3 * m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (c_to_b (3 * m + 3) 0 0 (e := e + m + 1))
  -- State: (0, 0+(3*m+3), 0, 0, e+m+1) = (0, 3*m+3, 0, 0, e+m+1)
  -- Phase 2: R5 + R3
  rw [show 0 + (3 * m + 3) = (3 * m + 2) + 1 from by ring]
  step fm
  rw [show e + m + 1 = (e + m) + 1 from by ring]
  step fm
  -- State: (3, 3*m+2, 0, 0, e+m)
  -- Phase 3: r1r3_loop
  apply stepStar_trans (r1r3_loop m 0 0 e)
  -- State: (3, 2, 0+3*m, 0+2*m, e)
  -- Phase 4: 2 R1 + 1 R2
  rw [show 0 + 3 * m = 3 * m from by ring,
      show 0 + 2 * m = 2 * m from by ring]
  step fm; step fm; step fm
  -- State: (0, 0, 3*m+3, 2*m+2, e+1)
  -- Phase 5: r3r2_loop with k=2*m+2
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_trans (r3r2_loop (2 * m + 2) (3 * m + 3) 0 e)
  -- State: (0, 0, 3*m+3+3*(2*m+2), 0, e+2*(2*m+2)+1) = (0, 0, 9*m+9, 0, e+4*m+5)
  rw [show 3 * m + 3 + 3 * (2 * m + 2) = 9 * (m + 1) from by ring,
      show e + 2 * (2 * m + 2) + 1 = e + 4 * m + 5 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 3⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m e, q = ⟨0, 0, 3 * (m + 1), 0, e + m + 1⟩)
  · intro q ⟨m, e, hq⟩; subst hq
    refine ⟨⟨0, 0, 9 * (m + 1), 0, e + 4 * m + 5⟩,
      ⟨3 * m + 2, e + m + 2, ?_⟩, main_trans m e⟩
    show (0, 0, 9 * (m + 1), 0, e + 4 * m + 5) =
         (0, 0, 3 * (3 * m + 2 + 1), 0, e + m + 2 + (3 * m + 2) + 1)
    ring_nf
  · exact ⟨0, 2, by norm_num⟩

end Sz22_2003_unofficial_782
