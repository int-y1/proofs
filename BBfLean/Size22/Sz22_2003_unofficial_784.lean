import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #784: [35/6, 56/55, 11/2, 3/7, 10/11]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  1 -1
-1  0  0  0  1
 0  1  0 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_784

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem d_to_b : ∀ k b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b + 1) d e); ring_nf; finish

theorem a_to_e : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a d (e + 1)); ring_nf; finish

theorem R2_chain : ∀ c a d e, ⟨a, 0, c, d, e + c⟩ [fm]⊢* ⟨a + 3 * c, 0, 0, d + c, e⟩ := by
  intro c; induction' c with c ih <;> intro a d e
  · exists 0
  · rw [show e + (c + 1) = (e + c) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 3) (d + 1) e); ring_nf; finish

theorem round_step (b c D E : ℕ) :
    ⟨0, b + 3, c + 1, D, E + 1⟩ [fm]⊢* ⟨0, b, c + 3, D + 4, E⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

theorem round_chain :
    ∀ k b c D E,
    ⟨0, 3 * k + b, c + 1, D, E + k⟩ [fm]⊢* ⟨0, b, c + 1 + 2 * k, D + 4 * k, E⟩ := by
  intro k; induction' k with k ih <;> intro b c D E
  · simp; exists 0
  · rw [show 3 * (k + 1) + b = (3 * k + b) + 3 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    apply stepStar_trans (round_step (3 * k + b) c D (E + k))
    rw [show c + 3 = (c + 2) + 1 from by ring]
    apply stepStar_trans (ih b (c + 2) (D + 4) E)
    ring_nf; finish

theorem d_to_b2 : ∀ k e, ⟨0, 0, 0, k, e⟩ [fm]⊢* ⟨0, k, 0, 0, e⟩ := by
  intro k e; have h := d_to_b k 0 0 e; simp only [Nat.zero_add] at h; exact h

theorem round_chain_0 :
    ∀ k c D E,
    ⟨0, 3 * k, c + 1, D, E + k⟩ [fm]⊢* ⟨0, 0, c + 1 + 2 * k, D + 4 * k, E⟩ := by
  intro k c D E; have h := round_chain k 0 c D E; simp only [Nat.add_zero] at h; exact h

theorem R2_chain_0 : ∀ c d e, ⟨0, 0, c, d, e + c⟩ [fm]⊢* ⟨3 * c, 0, 0, d + c, e⟩ := by
  intro c d e; have h := R2_chain c 0 d e; simp only [Nat.zero_add] at h; exact h

theorem a_to_e_0 : ∀ k d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + k⟩ := by
  intro k d e; have h := a_to_e k 0 d e; simp only [Nat.zero_add] at h; exact h

theorem tail_1 (c D E : ℕ) :
    ⟨0, 1, c + 1, D, E + c + 2⟩ [fm]⊢* ⟨3 * c + 5, 0, 0, D + c + 3, E⟩ := by
  rw [show E + c + 2 = (E + c + 1) + 1 from by ring]
  step fm; step fm
  rw [show E + c + 1 = E + (c + 1) from by ring]
  apply stepStar_trans (R2_chain (c + 1) 2 (D + 2) E)
  ring_nf; finish

theorem tail_2 (c D E : ℕ) :
    ⟨0, 2, c + 1, D, E + c + 3⟩ [fm]⊢* ⟨3 * c + 7, 0, 0, D + c + 5, E⟩ := by
  rw [show E + c + 3 = (E + c + 2) + 1 from by ring]
  step fm; step fm; step fm
  rw [show E + c + 2 = E + (c + 2) from by ring]
  apply stepStar_trans (R2_chain (c + 2) 1 (D + 3) E)
  ring_nf; finish

theorem trans_mod0 (q g : ℕ) :
    ⟨0, 0, 0, 3 * q + 1, 3 * q + g + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * q + 3, 6 * q + g + 6⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_b2 (3 * q + 1) (3 * q + g + 3))
  step fm; step fm
  rw [show 3 * q + g + 2 = (2 * q + g + 2) + q from by omega]
  apply stepStar_trans (round_chain_0 q 1 1 (2 * q + g + 2))
  rw [show 1 + 1 + 2 * q = (2 * q) + 1 + 1 from by omega,
      show 2 * q + g + 2 = g + ((2 * q) + 1 + 1) from by omega]
  apply stepStar_trans (R2_chain_0 ((2 * q) + 1 + 1) (1 + 4 * q) g)
  apply stepStar_trans (a_to_e_0 (3 * ((2 * q) + 1 + 1)) ((1 + 4 * q) + ((2 * q) + 1 + 1)) g)
  ring_nf; finish

theorem trans_mod1 (q g : ℕ) :
    ⟨0, 0, 0, 3 * q + 2, 3 * q + g + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * q + 5, 6 * q + g + 8⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_b2 (3 * q + 2) (3 * q + g + 4))
  step fm; step fm
  rw [show 3 * q + g + 3 = (2 * q + g + 3) + q from by omega]
  apply stepStar_trans (round_chain q 1 1 1 (2 * q + g + 3))
  rw [show 1 + 1 + 2 * q = (1 + 2 * q) + 1 from by omega,
      show 2 * q + g + 3 = g + (1 + 2 * q) + 2 from by omega]
  apply stepStar_trans (tail_1 (1 + 2 * q) (1 + 4 * q) g)
  apply stepStar_trans (a_to_e_0 (3 * (1 + 2 * q) + 5) ((1 + 4 * q) + (1 + 2 * q) + 3) g)
  ring_nf; finish

theorem trans_mod2 (q g : ℕ) :
    ⟨0, 0, 0, 3 * q + 3, 3 * q + g + 5⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * q + 7, 6 * q + g + 10⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_b2 (3 * q + 3) (3 * q + g + 5))
  step fm; step fm
  rw [show 3 * q + g + 4 = (2 * q + g + 4) + q from by omega]
  apply stepStar_trans (round_chain q 2 1 1 (2 * q + g + 4))
  rw [show 1 + 1 + 2 * q = (1 + 2 * q) + 1 from by omega,
      show 2 * q + g + 4 = g + (1 + 2 * q) + 3 from by omega]
  apply stepStar_trans (tail_2 (1 + 2 * q) (1 + 4 * q) g)
  apply stepStar_trans (a_to_e_0 (3 * (1 + 2 * q) + 7) ((1 + 4 * q) + (1 + 2 * q) + 5) g)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d g, q = ⟨0, 0, 0, d + 1, d + g + 3⟩)
  · intro c ⟨d, g, hq⟩; subst hq
    obtain ⟨q, rfl | rfl | rfl⟩ : ∃ q, d = 3 * q ∨ d = 3 * q + 1 ∨ d = 3 * q + 2 :=
      ⟨d / 3, by omega⟩
    · exact ⟨⟨0, 0, 0, 6 * q + 3, 6 * q + g + 6⟩,
        ⟨6 * q + 2, g + 1, by ring_nf⟩, trans_mod0 q g⟩
    · refine ⟨⟨0, 0, 0, 6 * q + 5, 6 * q + g + 8⟩,
        ⟨6 * q + 4, g + 1, by ring_nf⟩, ?_⟩
      rw [show 3 * q + 1 + 1 = 3 * q + 2 from by ring,
          show 3 * q + 1 + g + 3 = 3 * q + g + 4 from by ring]
      exact trans_mod1 q g
    · refine ⟨⟨0, 0, 0, 6 * q + 7, 6 * q + g + 10⟩,
        ⟨6 * q + 6, g + 1, by ring_nf⟩, ?_⟩
      rw [show 3 * q + 2 + 1 = 3 * q + 3 from by ring,
          show 3 * q + 2 + g + 3 = 3 * q + g + 5 from by ring]
      exact trans_mod2 q g
  · exact ⟨0, 0, by ring_nf⟩
