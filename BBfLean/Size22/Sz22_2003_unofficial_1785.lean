import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1785: [9/10, 4/21, 77/2, 25/7, 14/11]

Vector representation:
```
-1  2 -1  0  0
 2 -1  0 -1  0
-1  0  0  1  1
 0  0  2 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1785

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (d + 1) (e + 1)); ring_nf; finish

theorem r4_drain : ∀ k, ∀ c e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c + 2) e); ring_nf; finish

theorem inner_round : ∀ k, ∀ b e, ⟨0, b, c + 3 * k, 0, e + k⟩ [fm]⊢* ⟨0, b + 5 * k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (b + 5) e); ring_nf; finish

theorem c2_end : ⟨0, b, 2, 0, e + 1⟩ [fm]⊢* ⟨1, b + 3, 0, 0, e⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem c1_end : ⟨0, b, 1, 0, e + 1⟩ [fm]⊢* ⟨2, b + 1, 0, 0, e⟩ := by
  step fm; step fm; step fm; finish

theorem r3r2_drain : ∀ k, ∀ a e, ⟨a + 1, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]; step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1)); ring_nf; finish

theorem r5r2_start : ⟨0, b + 1, 0, 0, e + 1⟩ [fm]⊢* ⟨3, b, 0, 0, e⟩ := by
  step fm; step fm; finish

theorem main_mod1 : ⟨3 * m + 1, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨10 * m + 4, 0, 0, 0, E + 11 * m + 3⟩ := by
  rw [show (3 * m + 1 : ℕ) = (3 * m) + 1 from by ring]; step fm
  show ⟨3 * m, 0, 0, 1, E + 1⟩ [fm]⊢* ⟨10 * m + 4, 0, 0, 0, E + 11 * m + 3⟩
  apply stepStar_trans
  · rw [show (3 * m : ℕ) = 0 + 3 * m from by ring]
    exact r3_drain (3 * m) 1 (E + 1)
  apply stepStar_trans
  · rw [show 1 + 3 * m = 0 + (3 * m + 1) from by ring,
        show E + 1 + 3 * m = E + 3 * m + 1 from by ring]
    exact r4_drain (3 * m + 1) 0 (E + 3 * m + 1)
  apply stepStar_trans
  · rw [show 0 + 2 * (3 * m + 1) = 2 + 3 * (2 * m) from by ring,
        show E + 3 * m + 1 = (E + m + 1) + 2 * m from by ring]
    exact inner_round (2 * m) 0 (E + m + 1)
  apply stepStar_trans
  · rw [show 0 + 5 * (2 * m) = 10 * m from by ring]
    exact c2_end (b := 10 * m) (e := E + m)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 10 * m + 3 = 0 + (10 * m + 3) from by ring]
  apply stepStar_trans (r3r2_drain (10 * m + 3) 0 (E + m))
  ring_nf; finish

theorem main_mod2 : ⟨3 * m + 2, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨10 * m + 8, 0, 0, 0, E + 11 * m + 6⟩ := by
  rw [show (3 * m + 2 : ℕ) = (3 * m + 1) + 1 from by ring]; step fm
  show ⟨3 * m + 1, 0, 0, 1, E + 1⟩ [fm]⊢* ⟨10 * m + 8, 0, 0, 0, E + 11 * m + 6⟩
  apply stepStar_trans
  · rw [show (3 * m + 1 : ℕ) = 0 + (3 * m + 1) from by ring]
    exact r3_drain (3 * m + 1) 1 (E + 1)
  apply stepStar_trans
  · rw [show 1 + (3 * m + 1) = 0 + (3 * m + 2) from by ring,
        show E + 1 + (3 * m + 1) = E + 3 * m + 2 from by ring]
    exact r4_drain (3 * m + 2) 0 (E + 3 * m + 2)
  apply stepStar_trans
  · rw [show 0 + 2 * (3 * m + 2) = 1 + 3 * (2 * m + 1) from by ring,
        show E + 3 * m + 2 = (E + m + 1) + (2 * m + 1) from by ring]
    exact inner_round (2 * m + 1) 0 (E + m + 1)
  apply stepStar_trans
  · rw [show 0 + 5 * (2 * m + 1) = 10 * m + 5 from by ring]
    exact c1_end (b := 10 * m + 5) (e := E + m)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 10 * m + 5 + 1 = 0 + (10 * m + 6) from by ring]
  apply stepStar_trans (r3r2_drain (10 * m + 6) 1 (E + m))
  ring_nf; finish

theorem main_mod0 : ⟨3 * m + 3, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨10 * m + 12, 0, 0, 0, E + 11 * m + 9⟩ := by
  rw [show (3 * m + 3 : ℕ) = (3 * m + 2) + 1 from by ring]; step fm
  show ⟨3 * m + 2, 0, 0, 1, E + 1⟩ [fm]⊢* ⟨10 * m + 12, 0, 0, 0, E + 11 * m + 9⟩
  apply stepStar_trans
  · rw [show (3 * m + 2 : ℕ) = 0 + (3 * m + 2) from by ring]
    exact r3_drain (3 * m + 2) 1 (E + 1)
  apply stepStar_trans
  · rw [show 1 + (3 * m + 2) = 0 + (3 * m + 3) from by ring,
        show E + 1 + (3 * m + 2) = E + 3 * m + 3 from by ring]
    exact r4_drain (3 * m + 3) 0 (E + 3 * m + 3)
  apply stepStar_trans
  · rw [show 0 + 2 * (3 * m + 3) = 0 + 3 * (2 * m + 2) from by ring,
        show E + 3 * m + 3 = (E + m + 1) + (2 * m + 2) from by ring]
    exact inner_round (2 * m + 2) 0 (E + m + 1)
  apply stepStar_trans
  · rw [show 0 + 5 * (2 * m + 2) = (10 * m + 9) + 1 from by ring,
        show (E + m + 1 : ℕ) = (E + m) + 1 from by ring]
    exact r5r2_start (b := 10 * m + 9) (e := E + m)
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 10 * m + 9 = 0 + (10 * m + 9) from by ring]
  apply stepStar_trans (r3r2_drain (10 * m + 9) 2 (E + m))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 3⟩) (by execute fm 12)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩)
  · intro c ⟨a, e, hq⟩; subst hq
    obtain ⟨k, rfl | rfl | rfl⟩ : ∃ k, a = 3 * k ∨ a = 3 * k + 1 ∨ a = 3 * k + 2 :=
      ⟨a / 3, by omega⟩
    · exact ⟨⟨10 * k + 4, 0, 0, 0, e + 11 * k + 3⟩,
        ⟨10 * k + 3, e + 11 * k + 3, rfl⟩, main_mod1⟩
    · exact ⟨⟨10 * k + 8, 0, 0, 0, e + 11 * k + 6⟩,
        ⟨10 * k + 7, e + 11 * k + 6, rfl⟩, main_mod2⟩
    · exact ⟨⟨10 * k + 12, 0, 0, 0, e + 11 * k + 9⟩,
        ⟨10 * k + 11, e + 11 * k + 9, rfl⟩, main_mod0⟩
  · exact ⟨3, 3, rfl⟩
