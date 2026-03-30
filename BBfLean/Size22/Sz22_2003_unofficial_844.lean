import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #844: [36/35, 5/22, 49/2, 11/3, 10/7]

Vector representation:
```
 2  2 -1 -1  0
-1  0  1  0 -1
-1  0  0  2  0
 0 -1  0  0  1
 1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_844

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R5 step helper.
theorem r5_step : ⟨0, 0, 0, d + 1, e⟩ [fm]⊢ ⟨1, 0, 1, d, e⟩ := by
  rcases e with _ | e
  · simp [fm]
  · simp [fm]

-- R3 repeated: drain a to d.
theorem r3_drain : ∀ k, ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (d := d + 2))
    ring_nf; finish

-- R4 repeated: drain b to e.
theorem r4_drain : ∀ k, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b) (e := e + 1))
    ring_nf; finish

-- R1/R2 interleaved chain.
theorem r1r2_chain : ∀ k, ∀ a b d e, ⟨a, b, 1, d + k, e + k⟩ [fm]⊢* ⟨a + k, b + 2 * k, 1, d, e⟩ := by
  intro k; induction' k with k ih
  · intro a b d e; exists 0
  · intro a b d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 1) (b + 2) d e)
    ring_nf; finish

-- R1 step helper.
theorem r1_step_e0 : ⟨a, b, 1, d + 1, 0⟩ [fm]⊢ ⟨a + 2, b + 2, 0, d, 0⟩ := by
  simp [fm]

-- Full phase from R5 through everything.
theorem full_phase : ⟨0, 0, 0, d + e + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2 * e + 6, 2 * e + 2⟩ := by
  rw [show d + e + 2 = (d + e + 1) + 1 from by ring]
  apply step_stepStar_stepPlus r5_step
  -- Now at (1, 0, 1, d+e+1, e).
  -- R1/R2 chain for e rounds.
  have h1 : ⟨1, 0, 1, (d + 1) + e, 0 + e⟩ [fm]⊢* ⟨1 + e, 0 + 2 * e, 1, d + 1, 0⟩ :=
    r1r2_chain e 1 0 (d + 1) 0
  rw [show (d + 1) + e = d + e + 1 from by ring, show 0 + e = e from by ring] at h1
  apply stepStar_trans h1
  rw [show 0 + 2 * e = 2 * e from by ring]
  -- R1 step.
  have h2 : ⟨1 + e, 2 * e, 1, d + 1, 0⟩ [fm]⊢ ⟨1 + e + 2, 2 * e + 2, 0, d, 0⟩ :=
    r1_step_e0
  apply stepStar_trans (step_stepStar h2)
  -- R3 drain.
  rw [show 1 + e + 2 = 0 + (e + 3) from by ring, show 2 * e + 2 = 2 * e + 2 from rfl]
  apply stepStar_trans (r3_drain (e + 3) (a := 0) (b := 2 * e + 2) (d := d))
  rw [show d + 2 * (e + 3) = d + 2 * e + 6 from by ring]
  -- R4 drain.
  rw [show 2 * e + 2 = 0 + (2 * e + 2) from by ring]
  apply stepStar_trans (r4_drain (2 * e + 2) (b := 0) (d := d + 2 * e + 6) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + e + 2, e⟩)
  · intro c ⟨d, e, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, d + 2 * e + 6, 2 * e + 2⟩,
      ⟨d + 2, 2 * e + 2, by ring_nf⟩, full_phase⟩
  · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_844
