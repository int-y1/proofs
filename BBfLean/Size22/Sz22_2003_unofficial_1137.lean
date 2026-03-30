import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1137: [5/6, 44/35, 49/2, 9/11, 10/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  2  0  0 -1
 1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1137

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 chain: (0, b, 0, D, e+k) →* (0, b+2k, 0, D, e).
theorem e_to_b : ∀ k b e, ⟨(0 : ℕ), b, 0, D, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, D, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) e)
    ring_nf; finish

-- R3 drain: (a+k, 0, 0, d, e) →* (a, 0, 0, d+2*k, e).
theorem r3_drain : ∀ k a d, ⟨a + k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2))
    ring_nf; finish

-- R2 chain when b=0: (a, 0, c+k, d+k, e) →* (a+2k, 0, c, d, e+k).
theorem r2_chain : ∀ k a c d e, ⟨a, (0 : ℕ), c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

-- R2+R1+R1 interleaving loop.
theorem r2r1r1_chain : ∀ k b c d e, ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨0, b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = b + 2 * k + 2 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    ring_nf; finish

-- Interleave+drain after R4 phase.
-- From (0, 2E+2, 0, D+2E+6, 0) →* (0, 0, 0, D+4E+12, 2E+3).
-- Interleave:
--   R5+R1: (0, (2E+1)+1, 0, (D+2E+5)+1, 0) → ... → (0, 2E+1, 2, D+2E+5, 0)
--   r2r1r1 E rounds: (0, 1+2E, 1+1, (D+E+5)+E, 0) →* (0, 1, E+2, D+E+5, E)
--   R2+R1: (0, 1, (E+1)+1, (D+E+4)+1, E) → ... → (1, 0, E+2, D+E+4, E+1)
--   R2 chain E+2: (1, 0, 0+(E+2), (D+2)+(E+2), E+1) →* (2E+5, 0, 0, D+2, 2E+3)
-- Drain:
--   R3 drain 2E+5: (0+(2E+5), 0, 0, D+2, 2E+3) →* (0, 0, 0, D+4E+12, 2E+3)
theorem phase2 (D E : ℕ) :
    ⟨(0 : ℕ), 2 * E + 2, 0, D + 2 * E + 6, 0⟩ [fm]⊢* ⟨0, 0, 0, D + 4 * E + 12, 2 * E + 3⟩ := by
  -- R5+R1
  rw [show 2 * E + 2 = (2 * E + 1) + 1 from by ring,
      show D + 2 * E + 6 = (D + 2 * E + 5) + 1 from by ring]
  step fm; step fm
  -- r2r1r1_chain E rounds
  rw [show 2 * E + 1 = 1 + 2 * E from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show D + 2 * E + 5 = (D + E + 5) + E from by ring]
  apply stepStar_trans (r2r1r1_chain E 1 1 (D + E + 5) 0)
  -- R2+R1
  rw [show 1 + E + 1 = (E + 1) + 1 from by ring,
      show D + E + 5 = (D + E + 4) + 1 from by ring]
  -- Need to handle 0 + E
  have h0E : (0 : ℕ) + E = E := Nat.zero_add E
  rw [h0E]
  step fm; step fm
  -- R2 chain (E+2 steps)
  rw [show E + 1 + 1 = 0 + (E + 2) from by ring,
      show D + E + 4 = (D + 2) + (E + 2) from by ring]
  apply stepStar_trans (r2_chain (E + 2) 1 0 (D + 2) (E + 1))
  -- R3 drain (2E+5 steps)
  rw [show 1 + 2 * (E + 2) = 0 + (2 * E + 5) from by ring,
      show E + 1 + (E + 2) = 2 * E + 3 from by ring]
  apply stepStar_trans (r3_drain (2 * E + 5) 0 (D + 2) (e := 2 * E + 3))
  ring_nf; finish

-- Full cycle: (0, 0, 0, D+2E+6, E+1) →⁺ (0, 0, 0, D+4E+12, 2E+3).
theorem full_cycle (D E : ℕ) :
    ⟨(0 : ℕ), 0, 0, D + 2 * E + 6, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, D + 4 * E + 12, 2 * E + 3⟩ := by
  apply step_stepStar_stepPlus
  · -- First R4 step
    show ⟨(0 : ℕ), 0, 0, D + 2 * E + 6, E + 1⟩ [fm]⊢ ⟨0, 2, 0, D + 2 * E + 6, E⟩
    simp [fm]
  -- Remaining E R4 steps
  have h_r4 : ⟨(0 : ℕ), 2, 0, D + 2 * E + 6, 0 + E⟩ [fm]⊢* ⟨0, 2 + 2 * E, 0, D + 2 * E + 6, 0⟩ :=
    e_to_b E 2 0
  rw [Nat.zero_add] at h_r4
  apply stepStar_trans h_r4
  rw [show 2 + 2 * E = 2 * E + 2 from by ring]
  exact phase2 D E

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 6, 1⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D + 2 * E + 6, E + 1⟩)
  · intro c ⟨D, E, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, D + 4 * E + 12, 2 * E + 3⟩,
      ⟨D + 2, 2 * E + 2, by ring_nf⟩,
      full_cycle D E⟩
  · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_1137
