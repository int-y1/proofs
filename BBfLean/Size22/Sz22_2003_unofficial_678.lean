import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #678: [35/6, 3/385, 4/5, 77/2, 25/7]

Vector representation:
```
-1 -1  1  1  0
 0  1 -1 -1 -1
 2  0 -1  0  0
-1  0  0  1  1
 0  0  2 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_678

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

-- R4 chain: (a, 0, 0, d, e) →* (0, 0, 0, d+a, e+a)
theorem r4_chain : ∀ a, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + a, e + a⟩ := by
  intro a; induction' a with a ih generalizing d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1) (e := e + 1))
    ring_nf; finish

-- R5+R2+R2 one round: (0, b, 0, D+3, E+2) →* (0, b+2, 0, D, E)
theorem r5r2r2_round : ⟨0, b, 0, D + 3, E + 2⟩ [fm]⊢* ⟨0, b + 2, 0, D, E⟩ := by
  step fm; step fm; step fm; finish

-- R5+R2+R2 loop: k rounds
theorem r5r2r2_loop : ∀ k, ⟨0, b, 0, D + 3 * k, E + 2 * k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, D, E⟩ := by
  intro k; induction' k with k ih generalizing b D E
  · exists 0
  · rw [show D + 3 * (k + 1) = (D + 3) + 3 * k from by ring,
        show E + 2 * (k + 1) = (E + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (b := b) (D := D + 3) (E := E + 2))
    apply stepStar_trans (r5r2r2_round (b := b + 2 * k) (D := D) (E := E))
    ring_nf; finish

-- R5+R2 last step: (0, b, 0, D+2, 1) →* (0, b+1, 1, D, 0)
theorem r5r2_last : ⟨0, b, 0, D + 2, 1⟩ [fm]⊢* ⟨0, b + 1, 1, D, 0⟩ := by
  step fm; step fm; finish

-- R1+R1+R3 loop: (2, 2*k+1, c, D, 0) →* (1, 0, c+k+1, D+2*k+1, 0)
theorem r1r1r3_loop : ∀ k, ⟨2, 2 * k + 1, c, D, 0⟩ [fm]⊢* ⟨1, 0, c + k + 1, D + 2 * k + 1, 0⟩ := by
  intro k; induction' k with k ih generalizing c D
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c := c + 1) (D := D + 2))
    ring_nf; finish

-- R3 chain: (a, 0, c, D, 0) →* (a+2*c, 0, 0, D, 0)
theorem r3_chain : ∀ c, ⟨a, 0, c, D, 0⟩ [fm]⊢* ⟨a + 2 * c, 0, 0, D, 0⟩ := by
  intro c; induction' c with c ih generalizing a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

-- Main transition: (2*m+3, 0, 0, d, 0) →⁺ (2*m+5, 0, 0, d+m+1, 0) when d ≥ m+2
theorem main_trans (hd : d ≥ m + 2) :
    ⟨2 * m + 3, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2 * m + 5, 0, 0, d + m + 1, 0⟩ := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + (m + 2) := ⟨d - (m + 2), by omega⟩
  -- Phase 1: first R4 step (establishes ⊢⁺)
  apply step_stepStar_stepPlus
  · show (⟨(2 * m + 2) + 1, 0, 0, d' + (m + 2), 0⟩ : Q) [fm]⊢
      ⟨2 * m + 2, 0, 0, d' + (m + 2) + 1, 0 + 1⟩
    rfl
  -- Phase 1 continued: remaining 2m+2 R4 steps
  apply stepStar_trans (r4_chain (2 * m + 2) (d := d' + (m + 2) + 1) (e := 0 + 1))
  -- State: (0, 0, 0, d'+(m+2)+1+(2m+2), 1+(2m+2)) = (0, 0, 0, d'+3m+5, 2m+3)
  -- Rewrite as: (0, 0, 0, (d'+2)+3*(m+1), 1+2*(m+1))
  rw [show d' + (m + 2) + 1 + (2 * m + 2) = (d' + 2) + 3 * (m + 1) from by ring,
      show 0 + 1 + (2 * m + 2) = 1 + 2 * (m + 1) from by ring]
  -- Phase 2: R5+R2+R2 loop (m+1 rounds)
  apply stepStar_trans (r5r2r2_loop (m + 1) (b := 0) (D := d' + 2) (E := 1))
  -- State: (0, 2*(m+1), 0, d'+2, 1) = (0, 2m+2, 0, d'+2, 1)
  rw [show (0 : ℕ) + 2 * (m + 1) = 2 * m + 2 from by ring,
      show d' + 2 = d' + 0 + 2 from by ring]
  -- Phase 2b: R5+R2 last step
  apply stepStar_trans (r5r2_last (b := 2 * m + 2) (D := d' + 0))
  rw [show 2 * m + 2 + 1 = 2 * m + 3 from by ring,
      show d' + 0 = d' from by ring]
  -- Phase 3: R3 step (0, 2m+3, 1, d', 0) → (2, 2m+3, 0, d', 0)
  apply stepStar_trans
    (step_stepStar (show (⟨0, 2 * m + 3, 1, d', 0⟩ : Q) [fm]⊢
      ⟨2, 2 * m + 3, 0, d', 0⟩ from by simp [fm]))
  -- Phase 4: R1+R1+R3 loop (m+1 rounds)
  rw [show (2 * m + 3 : ℕ) = 2 * (m + 1) + 1 from by ring]
  apply stepStar_trans (r1r1r3_loop (m + 1) (c := 0) (D := d'))
  -- State: (1, 0, m+2, d'+2m+3, 0)
  rw [show 0 + (m + 1) + 1 = m + 2 from by ring,
      show d' + 2 * (m + 1) + 1 = d' + 2 * m + 3 from by ring]
  -- Phase 5: R3 chain (m+2 steps)
  show ⟨1, 0, m + 2, d' + 2 * m + 3, 0⟩ [fm]⊢* _
  apply stepStar_trans (r3_chain (m + 2) (a := 1) (D := d' + 2 * m + 3))
  rw [show 1 + 2 * (m + 2) = 2 * m + 5 from by ring,
      show d' + 2 * m + 3 = d' + (m + 2) + m + 1 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 2, 0⟩)
  · execute fm 24
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m d, q = ⟨2 * m + 3, 0, 0, d, 0⟩ ∧ d ≥ m + 2)
  · intro c ⟨m, d, hq, hd⟩; subst hq
    exact ⟨⟨2 * m + 5, 0, 0, d + m + 1, 0⟩,
      ⟨m + 1, d + m + 1, by ring_nf, by omega⟩,
      main_trans hd⟩
  · exact ⟨0, 2, rfl, by omega⟩

end Sz22_2003_unofficial_678
