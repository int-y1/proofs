import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1313: [63/10, 1331/2, 2/33, 5/7, 15/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  3
 1 -1  0  0 -1
 0  0  1 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1313

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: transfer d to c.
theorem r4_chain : ∀ k c d e, ⟨(0 : ℕ), (0 : ℕ), c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R1-R3 interleaved chain: each round R1 then R3.
theorem r1r3_chain : ∀ k j c e, ⟨1, j, c + k, j, e + k⟩ [fm]⊢* ⟨1, j + k, c, j + k, e⟩ := by
  intro k; induction' k with k ih <;> intro j c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (j + 1) c e)
    ring_nf; finish

-- R3-R2 chain: each round R3 then R2, draining b.
theorem r3r2_chain : ∀ k d e, ⟨(0 : ℕ), k, (0 : ℕ), d, e + 1⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih d (e + 2))
    ring_nf; finish

-- Main transition: (0, 0, 0, d, e+d+3) ⊢⁺ (0, 0, 0, d+1, e+2d+5)
theorem main_trans (d e : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, d, e + d + 3⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 0, d + 1, e + 2 * d + 5⟩ := by
  -- Phase 1: R4 chain (d steps), moving d to c
  have h1 : ⟨(0 : ℕ), (0 : ℕ), 0, d, e + d + 3⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), d, 0, e + d + 3⟩ := by
    have := r4_chain d 0 0 (e + d + 3)
    simp only [Nat.zero_add] at this; exact this
  apply stepStar_stepPlus_stepPlus h1
  -- State: (0, 0, d, 0, e+d+3)
  -- Phase 2: R5 (1 step)
  rw [show e + d + 3 = (e + d + 2) + 1 from by ring]
  step fm
  -- State: (0, 1, d+1, 0, e+d+2)
  -- Phase 3: R3 (1 step)
  rw [show e + d + 2 = (e + d + 1) + 1 from by ring]
  step fm
  -- State: (1, 0, d+1, 0, e+d+1)
  -- Phase 4: R1-R3 chain (d rounds)
  rw [show d + 1 = 1 + d from by ring,
      show e + d + 1 = (e + 1) + d from by ring]
  apply stepStar_trans (r1r3_chain d 0 1 (e + 1))
  rw [show (0 : ℕ) + d = d from by ring]
  -- State: (1, d, 1, d, e+1)
  -- Phase 5: Final R1 (1 step)
  step fm
  -- State: (0, d+2, 0, d+1, e+1)
  -- Phase 6: R3-R2 drain (d+2 rounds)
  apply stepStar_trans (r3r2_chain (d + 2) (d + 1) e)
  rw [show e + 2 * (d + 2) + 1 = e + 2 * d + 5 from by ring]
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 3⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e + d + 3⟩)
  · intro c ⟨d, e, hc⟩; subst hc
    exact ⟨⟨0, 0, 0, d + 1, e + 2 * d + 5⟩, ⟨d + 1, e + d + 1, by ring_nf⟩, main_trans d e⟩
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_1313
