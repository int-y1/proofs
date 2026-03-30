import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1138: [5/6, 44/35, 49/2, 9/11, 15/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  2  0  0 -1
 0  1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1138

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r3_step (a c e : ℕ) :
    ⟨a + 1, 0, c, 0, e⟩ [fm]⊢ ⟨a, 0, c, 2, e⟩ := by
  simp only [fm]

theorem e_to_b : ∀ k b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

theorem a_to_d : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2) e)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k b c d e,
    ⟨0, b + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨0, b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    ring_nf; finish

theorem r2_chain : ∀ k a c d e,
    ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

theorem tail_step (a c e : ℕ) :
    ⟨a, 0, c + 2, 2, e⟩ [fm]⊢* ⟨a + 3, 0, c, 2, e + 2⟩ := by
  step fm; step fm
  rw [show a + 1 + 1 + 2 = (a + 3) + 1 from by ring,
      show e + 1 + 1 = e + 2 from by ring]
  exact step_stepStar (r3_step (a + 3) c (e + 2))

theorem tail_even : ∀ k a e,
    ⟨a, 0, 2 * k, 2, e⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, 2, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show 2 * (k + 1) = k * 2 + 2 from by ring]
    apply stepStar_trans (tail_step a (k * 2) e)
    rw [show k * 2 = 2 * k from by ring]
    apply stepStar_trans (ih (a + 3) (e + 2))
    ring_nf; finish

theorem tail_odd : ∀ k a e,
    ⟨a, 0, 2 * k + 1, 2, e⟩ [fm]⊢* ⟨a + 3 * k + 2, 0, 0, 1, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = (k * 2 + 1) + 2 from by ring]
    apply stepStar_trans (tail_step a (k * 2 + 1) e)
    rw [show k * 2 + 1 = 2 * k + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (e + 2))
    ring_nf; finish

-- Phase 6-9 helper for even case
theorem phases_6_9_even (E D' m : ℕ) (hD : D' ≤ E + 1) (hm : E + 2 - D' = 2 * m) :
    ⟨1, 0, E + 2, D', E + 2⟩ [fm]⊢* ⟨0, 0, 0, D' + 3 * E + 8, 2 * E + 4⟩ := by
  set C := E + 2 - D' with hC_def
  have hCD : C + D' = E + 2 := by omega
  have hCE : C = 2 * m := hm
  -- r2_chain: (1, 0, C+D', 0+D', E+2) ⊢* (1+2D', 0, C, 0, E+2+D')
  have h1 : ⟨1, 0, C + D', D' + 0, E + 2⟩ [fm]⊢* ⟨1 + 2 * D', 0, C, 0, E + 2 + D'⟩ := by
    rw [show D' + 0 = 0 + D' from by ring]
    exact r2_chain D' 1 C 0 (E + 2)
  rw [hCD, show D' + 0 = D' from by ring] at h1
  apply stepStar_trans h1
  -- R3 step
  apply stepStar_trans
  · rw [show 1 + 2 * D' = (2 * D') + 1 from by ring]
    exact step_stepStar (r3_step (2 * D') C (E + 2 + D'))
  -- tail_even
  apply stepStar_trans
  · rw [hCE]
    exact tail_even m (2 * D') (E + 2 + D')
  -- a_to_d
  rw [show 2 * D' + 3 * m = 0 + (2 * D' + 3 * m) from by ring]
  apply stepStar_trans (a_to_d (2 * D' + 3 * m) 0 2 (E + 2 + D' + 2 * m))
  rw [show 2 + 2 * (2 * D' + 3 * m) = D' + 3 * E + 8 from by omega,
      show E + 2 + D' + 2 * m = 2 * E + 4 from by omega]
  finish

-- Phase 6-9 helper for odd case
theorem phases_6_9_odd (E D' m : ℕ) (hD : D' ≤ E + 1) (hm : E + 2 - D' = 2 * m + 1) :
    ⟨1, 0, E + 2, D', E + 2⟩ [fm]⊢* ⟨0, 0, 0, D' + 3 * E + 8, 2 * E + 4⟩ := by
  set C := E + 2 - D' with hC_def
  have hCD : C + D' = E + 2 := by omega
  have hCO : C = 2 * m + 1 := hm
  have h1 : ⟨1, 0, C + D', D' + 0, E + 2⟩ [fm]⊢* ⟨1 + 2 * D', 0, C, 0, E + 2 + D'⟩ := by
    rw [show D' + 0 = 0 + D' from by ring]
    exact r2_chain D' 1 C 0 (E + 2)
  rw [hCD, show D' + 0 = D' from by ring] at h1
  apply stepStar_trans h1
  apply stepStar_trans
  · rw [show 1 + 2 * D' = (2 * D') + 1 from by ring]
    exact step_stepStar (r3_step (2 * D') C (E + 2 + D'))
  apply stepStar_trans
  · rw [hCO]
    exact tail_odd m (2 * D') (E + 2 + D')
  rw [show 2 * D' + 3 * m + 2 = 0 + (2 * D' + 3 * m + 2) from by ring]
  apply stepStar_trans (a_to_d (2 * D' + 3 * m + 2) 0 1 (E + 2 + D' + (2 * m + 1)))
  rw [show 1 + 2 * (2 * D' + 3 * m + 2) = D' + 3 * E + 8 from by omega,
      show E + 2 + D' + (2 * m + 1) = 2 * E + 4 from by omega]
  finish

-- Phase 6-9 helper for D' = E + 2 (full drain, no tail)
theorem phases_6_9_full (E : ℕ) :
    ⟨1, 0, E + 2, E + 2, E + 2⟩ [fm]⊢* ⟨0, 0, 0, 4 * E + 10, 2 * E + 4⟩ := by
  -- r2_chain with k = E+2: (1, 0, (E+2), (E+2), E+2) ⊢* (1+2*(E+2), 0, 0, 0, E+2+(E+2))
  have h1 : ⟨1, 0, 0 + (E + 2), 0 + (E + 2), E + 2⟩ [fm]⊢*
      ⟨1 + 2 * (E + 2), 0, 0, 0, E + 2 + (E + 2)⟩ :=
    r2_chain (E + 2) 1 0 0 (E + 2)
  rw [show 0 + (E + 2) = E + 2 from by ring,
      show 1 + 2 * (E + 2) = (2 * E + 5) from by ring,
      show E + 2 + (E + 2) = 2 * E + 4 from by ring] at h1
  apply stepStar_trans h1
  -- a_to_d: (2E+5, 0, 0, 0, 2E+4) ⊢* (0, 0, 0, 2*(2E+5), 2E+4)
  rw [show (2 * E + 5 : ℕ) = 0 + (2 * E + 5) from by ring]
  apply stepStar_trans (a_to_d (2 * E + 5) 0 0 (2 * E + 4))
  rw [show 0 + 2 * (2 * E + 5) = 4 * E + 10 from by ring]
  finish

-- Phases 1-5: common prefix
theorem phases_1_5 (E D' : ℕ) :
    ⟨0, 0, 0, D' + E + 3, E + 1⟩ [fm]⊢⁺ ⟨1, 0, E + 2, D', E + 2⟩ := by
  -- Phase 1: R4
  apply stepStar_stepPlus_stepPlus
  · rw [show (E + 1 : ℕ) = 0 + (E + 1) from by ring]
    exact e_to_b (E + 1) 0 (D' + E + 3) 0
  rw [show 0 + 2 * (E + 1) = 2 * E + 2 from by ring]
  -- Phase 2: R5
  apply step_stepStar_stepPlus (show ⟨0, 2 * E + 2, 0, D' + E + 3, 0⟩ [fm]⊢
    ⟨0, 2 * E + 3, 1, D' + E + 2, 0⟩ from rfl)
  -- Phase 3: first R2+R1+R1 round
  apply stepStar_trans (step_stepStar (show ⟨0, 2 * E + 3, 1, D' + E + 2, 0⟩ [fm]⊢
    ⟨2, 2 * E + 3, 0, D' + E + 1, 1⟩ from rfl))
  apply stepStar_trans (step_stepStar (show ⟨2, 2 * E + 3, 0, D' + E + 1, 1⟩ [fm]⊢
    ⟨1, 2 * E + 2, 1, D' + E + 1, 1⟩ from rfl))
  apply stepStar_trans (step_stepStar (show ⟨1, 2 * E + 2, 1, D' + E + 1, 1⟩ [fm]⊢
    ⟨0, 2 * E + 1, 2, D' + E + 1, 1⟩ from rfl))
  -- Phase 4: r2r1r1 chain x E
  apply stepStar_trans
  · rw [show 2 * E + 1 = 1 + 2 * E from by ring,
        show D' + E + 1 = (D' + 1) + E from by ring]
    exact r2r1r1_chain E 1 1 (D' + 1) 1
  rw [show 1 + E + 1 = E + 2 from by ring,
      show D' + 1 = D' + 1 from rfl,
      show 1 + E = E + 1 from by ring]
  -- Phase 5: R2 + R1
  apply stepStar_trans (step_stepStar (show ⟨0, 1, E + 2, D' + 1, E + 1⟩ [fm]⊢
    ⟨2, 1, E + 1, D', E + 2⟩ from rfl))
  apply stepStar_trans (step_stepStar (show ⟨2, 1, E + 1, D', E + 2⟩ [fm]⊢
    ⟨1, 0, E + 2, D', E + 2⟩ from rfl))
  finish

-- Main transition (D' ≤ E + 2)
theorem main_trans (E D' : ℕ) (hD : D' ≤ E + 2) :
    ⟨0, 0, 0, D' + E + 3, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, D' + 3 * E + 8, 2 * E + 4⟩ := by
  apply stepPlus_stepStar_stepPlus (phases_1_5 E D')
  by_cases hD2 : D' ≤ E + 1
  · rcases Nat.even_or_odd (E + 2 - D') with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm
      exact phases_6_9_even E D' m hD2 hm
    · exact phases_6_9_odd E D' m hD2 hm
  · -- D' = E + 2
    have hD' : D' = E + 2 := by omega
    subst hD'
    rw [show (E + 2) + 3 * E + 8 = 4 * E + 10 from by ring]
    exact phases_6_9_full E

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ e + 2 ∧ d ≤ 2 * e + 3)
  · intro c ⟨d, e, hq, hd, hd2⟩; subst hq
    by_cases he : e = 0
    · subst he
      rcases (show d = 2 ∨ d = 3 from by omega) with rfl | rfl
      · exact ⟨_, ⟨5, 2, rfl, by omega, by omega⟩, by execute fm 7⟩
      · exact ⟨_, ⟨6, 2, rfl, by omega, by omega⟩, by execute fm 7⟩
    · rcases e with _ | E
      · omega
      · obtain ⟨D', rfl⟩ : ∃ D', d = D' + E + 3 := ⟨d - E - 3, by omega⟩
        have hD : D' ≤ E + 2 := by omega
        exact ⟨⟨0, 0, 0, D' + 3 * E + 8, 2 * E + 4⟩,
          ⟨D' + 3 * E + 8, 2 * E + 4, rfl, by omega, by omega⟩,
          main_trans E D' hD⟩
  · exact ⟨2, 0, rfl, by omega, by omega⟩
