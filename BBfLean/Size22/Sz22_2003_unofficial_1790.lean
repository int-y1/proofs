import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1790: [9/10, 44/21, 7/2, 5/11, 66/7]

Vector representation:
```
-1  2 -1  0  0
 2 -1  0 -1  1
-1  0  0  1  0
 0  0  1  0 -1
 1  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1790

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: move e to c
theorem e_to_c : ∀ k, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [show c + (k + 1) = (c + 1) + k from by ring]
    step fm
    exact ih (c := c + 1)

-- R3 chain: move a to d (when b=0, c=0)
theorem a_to_d : ∀ k, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih (d := d + 1)

-- R2 chain: consume d, when c=0
theorem r2_chain : ∀ k, ∀ a b e, ⟨a, b + k, 0, k, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring,
        show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    exact ih (a + 2) b (e + 1)

-- R3/R2 drain: alternating R3 and R2 when c=0, d=0
theorem r32_drain : ∀ k, ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show a + (k + 1) + 1 = (a + 1) + k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm
    exact ih (a := a + 1) (e := e + 1)

-- R1R1R2 chain: 3-step rounds (R1, R1, R2)
theorem r112_chain : ∀ k, ∀ b d e, ⟨2, b, 2 * k + 1, d + k, e⟩ [fm]⊢* ⟨2, b + 3 * k, 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring,
        show d + (k + 1) = d + k + 1 from by ring,
        show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    rw [show 2 * k + 1 + 1 = (2 * k + 1) + 1 from rfl]
    step fm
    rw [show b + 2 + 2 = b + 4 from by ring]
    apply stepStar_trans
    · apply step_stepStar
      show fm ⟨0, b + 4, 2 * k + 1, d + k + 1, e⟩ = some ⟨2, b + 3, 2 * k + 1, d + k, e + 1⟩
      simp [fm]
    exact ih (b + 3) d (e + 1)

-- Main transition
theorem main_trans (F G : ℕ) (hG : G ≤ 3 * F + 1) :
    ⟨0, 0, 0, G + F + 2, 2 * (F + 1)⟩ [fm]⊢⁺ ⟨0, 0, 0, G + 3 * F + 5, 4 * F + 6⟩ := by
  -- Phase 1: R4 chain + R5 + R1 + R2 = 4 steps beyond ⊢*
  -- We build up ⊢⁺ from c₀ to the end of Phase 4
  -- then ⊢* for Phases 5-9
  -- Phase 1 + 2: R4 chain then R5
  apply stepStar_stepPlus_stepPlus
  · -- ⊢*: (0,0,0,D,E) → (0,0,E,D,0)
    have h := e_to_c (2 * (F + 1)) (c := 0) (d := G + F + 2)
    simp only [Nat.zero_add] at h; exact h
  -- R5 step: (0,0,E,D+1,0) → (1,1,E,D,1)
  rw [show 2 * (F + 1) = 2 * F + 1 + 1 from by ring,
      show G + F + 2 = (G + F + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show (⟨0, 0, 2 * F + 1 + 1, (G + F + 1) + 1, 0⟩ : Q) [fm]⊢ ⟨1, 1, 2 * F + 1 + 1, G + F + 1, 1⟩ from by simp [fm])
  -- Phase 3: R1: (1,1,C+1,D,1) → (0,3,C,D,1)
  apply stepStar_trans (step_stepStar
    (show (⟨1, 1, 2 * F + 1 + 1, G + F + 1, 1⟩ : Q) [fm]⊢ ⟨0, 3, 2 * F + 1, G + F + 1, 1⟩ from by simp [fm]))
  -- Phase 4: R2
  rw [show G + F + 1 = (G + F) + 1 from by ring]
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨0, 3, 2 * F + 1, (G + F) + 1, 1⟩ : Q) [fm]⊢ ⟨2, 2, 2 * F + 1, G + F, 2⟩))
  -- Phase 5: R1R1R2 chain
  apply stepStar_trans (r112_chain F 2 G 2)
  -- Phase 6: final R1
  apply stepStar_trans (step_stepStar (by simp [fm] : (⟨2, 2 + 3 * F, 1, G, 2 + F⟩ : Q) [fm]⊢ ⟨1, 2 + 3 * F + 2, 0, G, 2 + F⟩))
  -- Phase 7: R2 chain
  apply stepStar_trans
  · rw [show 2 + 3 * F + 2 = (2 + 3 * F + 2 - G) + G from by omega]
    exact r2_chain G 1 (2 + 3 * F + 2 - G) (2 + F)
  -- Phase 8: R3/R2 drain
  apply stepStar_trans
  · rw [show 1 + 2 * G = 2 * G + 0 + 1 from by ring]
    exact r32_drain (2 + 3 * F + 2 - G) (a := 2 * G) (e := 2 + F + G)
  -- Phase 9: R3 chain
  rw [show 2 * G + (2 + 3 * F + 2 - G) + 1 = G + 3 * F + 5 from by omega,
      show 2 + F + G + (2 + 3 * F + 2 - G) = 4 * F + 6 from by omega]
  have h9 := a_to_d (G + 3 * F + 5) (d := 0) (e := 4 * F + 6)
  simp only [Nat.zero_add] at h9; exact h9

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ F G, q = ⟨0, 0, 0, G + F + 2, 2 * (F + 1)⟩ ∧ G ≤ 3 * F + 1)
  · intro c ⟨F, G, hq, hG⟩; subst hq
    refine ⟨⟨0, 0, 0, G + 3 * F + 5, 4 * F + 6⟩, ?_, main_trans F G hG⟩
    refine ⟨2 * F + 2, G + F + 1, ?_, by omega⟩
    show (⟨0, 0, 0, G + 3 * F + 5, 4 * F + 6⟩ : Q) = ⟨0, 0, 0, G + F + 1 + (2 * F + 2) + 2, 2 * (2 * F + 2 + 1)⟩
    simp only [Prod.mk.injEq, true_and]; constructor <;> ring
  · exact ⟨0, 0, rfl, by omega⟩
