import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1786: [9/10, 4/21, 77/2, 5/7, 14/11]

Vector representation:
```
-1  2 -1  0  0
 2 -1  0 -1  0
-1  0  0  1  1
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1786

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem d_to_c : ∀ k, ∀ c d, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

theorem full_round : ⟨0, b, c + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨0, b + 5, c, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem full_round_chain : ∀ k, ∀ b c e, ⟨0, b, c + 3 * k, 0, e + k⟩ [fm]⊢* ⟨0, b + 5 * k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans (stepPlus_stepStar (full_round (b := b) (c := c + 3 * k) (e := e + k)))
    apply stepStar_trans (ih (b + 5) c e)
    ring_nf; finish

theorem end_mod0 : ⟨0, b + 1, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨3, b, 0, 0, e⟩ := by
  step fm; step fm; finish

theorem end_mod1 : ⟨0, b, 1, 0, e + 1⟩ [fm]⊢⁺ ⟨2, b + 1, 0, 0, e⟩ := by
  step fm; step fm; step fm; finish

theorem end_mod2 : ⟨0, b, 2, 0, e + 1⟩ [fm]⊢⁺ ⟨2, b + 2, 0, 0, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem r3r2_drain : ∀ k, ∀ a e, ⟨a + 1, k + 1, 0, 0, e⟩ [fm]⊢* ⟨a + k + 2, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; step fm; finish
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1) (e + 1))
    ring_nf; finish

theorem main_trans_mod1 : ∀ k e, ⟨0, 0, 0, 3 * k + 1, e + k + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 5 * k + 3, e + 10 * k + 4⟩ := by
  intro k e
  rw [show (3 * k + 1 : ℕ) = 0 + (3 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (3 * k + 1) 0 0 (e := e + k + 1))
  rw [show 0 + (3 * k + 1) = 1 + 3 * k from by ring,
      show e + k + 1 = (e + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus (full_round_chain k 0 1 (e + 1))
  rw [show 0 + 5 * k = 5 * k from by ring]
  apply stepPlus_stepStar_stepPlus (end_mod1 (b := 5 * k) (e := e))
  apply stepStar_trans (r3r2_drain (5 * k) 1 e)
  rw [show 1 + 5 * k + 2 = 5 * k + 3 from by ring]
  apply stepStar_trans (r3_drain (5 * k + 3) 0 (e + 5 * k + 1))
  ring_nf; finish

theorem main_trans_mod2 : ∀ k e, ⟨0, 0, 0, 3 * k + 2, e + k + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 5 * k + 4, e + 10 * k + 7⟩ := by
  intro k e
  rw [show (3 * k + 2 : ℕ) = 0 + (3 * k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (3 * k + 2) 0 0 (e := e + k + 1))
  rw [show 0 + (3 * k + 2) = 2 + 3 * k from by ring,
      show e + k + 1 = (e + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus (full_round_chain k 0 2 (e + 1))
  rw [show 0 + 5 * k = 5 * k from by ring]
  apply stepPlus_stepStar_stepPlus (end_mod2 (b := 5 * k) (e := e))
  apply stepStar_trans (r3r2_drain (5 * k + 1) 1 (e + 1))
  rw [show 1 + (5 * k + 1) + 2 = 5 * k + 4 from by ring,
      show e + 1 + (5 * k + 1) + 1 = e + 5 * k + 3 from by ring]
  apply stepStar_trans (r3_drain (5 * k + 4) 0 (e + 5 * k + 3))
  ring_nf; finish

theorem main_trans_mod0 : ∀ k e, ⟨0, 0, 0, 3 * (k + 1), e + k + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 5 * k + 7, e + 10 * k + 11⟩ := by
  intro k e
  rw [show (3 * (k + 1) : ℕ) = 0 + 3 * (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (3 * (k + 1)) 0 0 (e := e + k + 2))
  rw [show 0 + 3 * (k + 1) = 0 + 3 * (k + 1) from by ring,
      show e + k + 2 = (e + 1) + (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (full_round_chain (k + 1) 0 0 (e + 1))
  rw [show 0 + 5 * (k + 1) = 5 * k + 4 + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (end_mod0 (b := 5 * k + 4) (e := e))
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2_drain (5 * k + 3) 2 e)
  rw [show 2 + (5 * k + 3) + 2 = 5 * k + 7 from by ring,
      show e + (5 * k + 3) + 1 = e + 5 * k + 4 from by ring]
  apply stepStar_trans (r3_drain (5 * k + 7) 0 (e + 5 * k + 4))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, d + e + 1⟩)
  · intro c ⟨d, e, hq⟩; subst hq
    obtain ⟨k, rfl | rfl | rfl⟩ : ∃ k, d = 3 * k ∨ d = 3 * k + 1 ∨ d = 3 * k + 2 := ⟨d / 3, by omega⟩
    · refine ⟨⟨0, 0, 0, 5 * k + 3, 12 * k + e + 4⟩,
        ⟨5 * k + 2, 7 * k + e + 1, by ring_nf⟩, ?_⟩
      rw [show 3 * k + e + 1 = (2 * k + e) + k + 1 from by ring,
          show (12 * k + e + 4 : ℕ) = (2 * k + e) + 10 * k + 4 from by ring]
      exact main_trans_mod1 k (2 * k + e)
    · refine ⟨⟨0, 0, 0, 5 * k + 4, 12 * k + e + 8⟩,
        ⟨5 * k + 3, 7 * k + e + 4, by ring_nf⟩, ?_⟩
      rw [show 3 * k + 1 + e + 1 = (2 * k + e + 1) + k + 1 from by ring,
          show (12 * k + e + 8 : ℕ) = (2 * k + e + 1) + 10 * k + 7 from by ring]
      exact main_trans_mod2 k (2 * k + e + 1)
    · refine ⟨⟨0, 0, 0, 5 * k + 7, 12 * k + e + 12⟩,
        ⟨5 * k + 6, 7 * k + e + 5, by ring_nf⟩, ?_⟩
      rw [show 3 * k + 2 + e + 1 = (2 * k + e + 1) + k + 2 from by ring,
          show (12 * k + e + 12 : ℕ) = (2 * k + e + 1) + 10 * k + 11 from by ring]
      exact main_trans_mod0 k (2 * k + e + 1)
  · exact ⟨0, 0, rfl⟩
