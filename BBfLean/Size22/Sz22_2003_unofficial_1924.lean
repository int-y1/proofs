import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1924: [9/70, 22/5, 25/21, 7/11, 21/2]

Vector representation:
```
-1  2 -1 -1  0
 1  0 -1  0  1
 0 -1  2 -1  0
 0  0  0  1 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1924

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih
  · intro d; exists 0
  · intro d; step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

theorem r1r1r3_chain : ∀ k a b, ⟨a + 2 * k, b, 2, d + 3 * k, 0⟩ [fm]⊢* ⟨a, b + 3 * k, 2, d, 0⟩ := by
  intro k; induction' k with k ih
  · intro a b; exists 0
  · intro a b
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 1 + 1 from by ring,
        show d + 3 * (k + 1) = (d + 3 * k) + 1 + 1 + 1 from by ring]
    step fm; step fm
    have h3 : ⟨a + 2 * k, b + 3 + 1, 0, d + 3 * k + 1, 0⟩ [fm]⊢ ⟨a + 2 * k, b + 3, 2, d + 3 * k, 0⟩ := by
      simp [fm]
    apply stepStar_trans (step_stepStar h3)
    apply stepStar_trans (ih a (b + 3))
    ring_nf; finish

theorem b_drain : ∀ k a e, ⟨a, k, 0, 0, e + 1⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih
  · intro a e; exists 0
  · intro a e
    step fm
    rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm; step fm
    rw [show a + 1 + 1 = a + 2 from by ring, show e + 1 + 1 = e + 2 from by ring]
    apply stepStar_trans (ih (a + 2) (e + 1))
    ring_nf; finish

theorem opening : ⟨a + 1, 0, 0, d + 1, 0⟩ [fm]⊢* ⟨a, 0, 2, d + 1, 0⟩ := by
  step fm
  rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
  step fm; finish

theorem rem0 : ⟨a, b, 2, 0, 0⟩ [fm]⊢* ⟨a + 2, b, 0, 0, 2⟩ := by
  step fm; step fm; finish

theorem rem1 : ⟨a + 1, b, 2, 1, 0⟩ [fm]⊢* ⟨a + 3, b + 1, 0, 0, 2⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem rem2 : ⟨a + 3, b, 2, 2, 0⟩ [fm]⊢* ⟨a + 2, b + 4, 0, 0, 2⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem trans_mod0 : ⟨a + 2 * k + 3, 0, 0, 0, 3 * k + 3⟩ [fm]⊢⁺
    ⟨a + 6 * k + 8, 0, 0, 0, 3 * k + 5⟩ := by
  rw [show 3 * k + 3 = (3 * k + 2) + 1 from by ring]
  refine step_stepStar_stepPlus (c₂ := ⟨a + 2 * k + 3, 0, 0, 1, 3 * k + 2⟩) (by simp [fm]) ?_
  apply stepStar_trans (e_to_d (3 * k + 2) 1 (a := a + 2 * k + 3))
  rw [show (1 : ℕ) + (3 * k + 2) = 3 * k + 3 from by ring,
      show a + 2 * k + 3 = (a + 2 * k + 2) + 1 from by ring,
      show 3 * k + 3 = (3 * k + 2) + 1 from by ring]
  apply stepStar_trans (opening (a := a + 2 * k + 2) (d := 3 * k + 2))
  rw [show a + 2 * k + 2 = a + 2 * (k + 1) from by ring,
      show (3 * k + 2) + 1 = 0 + 3 * (k + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (k + 1) a 0 (d := 0))
  rw [show (0 : ℕ) + 3 * (k + 1) = 3 * k + 3 from by ring]
  apply stepStar_trans (rem0 (a := a) (b := 3 * k + 3))
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (b_drain (3 * k + 3) (a + 2) 1)
  ring_nf; finish

theorem trans_mod1 : ⟨a + 2 * k + 4, 0, 0, 0, 3 * k + 4⟩ [fm]⊢⁺
    ⟨a + 6 * k + 11, 0, 0, 0, 3 * k + 6⟩ := by
  rw [show 3 * k + 4 = (3 * k + 3) + 1 from by ring]
  refine step_stepStar_stepPlus (c₂ := ⟨a + 2 * k + 4, 0, 0, 1, 3 * k + 3⟩) (by simp [fm]) ?_
  apply stepStar_trans (e_to_d (3 * k + 3) 1 (a := a + 2 * k + 4))
  rw [show (1 : ℕ) + (3 * k + 3) = 3 * k + 4 from by ring,
      show a + 2 * k + 4 = (a + 2 * k + 3) + 1 from by ring,
      show 3 * k + 4 = (3 * k + 3) + 1 from by ring]
  apply stepStar_trans (opening (a := a + 2 * k + 3) (d := 3 * k + 3))
  rw [show a + 2 * k + 3 = (a + 1) + 2 * (k + 1) from by ring,
      show (3 * k + 3) + 1 = 1 + 3 * (k + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (k + 1) (a + 1) 0 (d := 1))
  rw [show (0 : ℕ) + 3 * (k + 1) = 3 * k + 3 from by ring]
  apply stepStar_trans (rem1 (a := a) (b := 3 * k + 3))
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 3 * k + 3 + 1 = 3 * k + 4 from by ring]
  apply stepStar_trans (b_drain (3 * k + 4) (a + 3) 1)
  ring_nf; finish

theorem trans_mod2 : ⟨a + 2 * k + 8, 0, 0, 0, 3 * k + 8⟩ [fm]⊢⁺
    ⟨a + 6 * k + 22, 0, 0, 0, 3 * k + 12⟩ := by
  rw [show 3 * k + 8 = (3 * k + 7) + 1 from by ring]
  refine step_stepStar_stepPlus (c₂ := ⟨a + 2 * k + 8, 0, 0, 1, 3 * k + 7⟩) (by simp [fm]) ?_
  apply stepStar_trans (e_to_d (3 * k + 7) 1 (a := a + 2 * k + 8))
  rw [show (1 : ℕ) + (3 * k + 7) = 3 * k + 8 from by ring,
      show a + 2 * k + 8 = (a + 2 * k + 7) + 1 from by ring,
      show 3 * k + 8 = (3 * k + 7) + 1 from by ring]
  apply stepStar_trans (opening (a := a + 2 * k + 7) (d := 3 * k + 7))
  rw [show a + 2 * k + 7 = (a + 3) + 2 * (k + 2) from by ring,
      show (3 * k + 7) + 1 = 2 + 3 * (k + 2) from by ring]
  apply stepStar_trans (r1r1r3_chain (k + 2) (a + 3) 0 (d := 2))
  rw [show (0 : ℕ) + 3 * (k + 2) = 3 * k + 6 from by ring]
  apply stepStar_trans (rem2 (a := a) (b := 3 * k + 6))
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 3 * k + 6 + 4 = 3 * k + 10 from by ring]
  apply stepStar_trans (b_drain (3 * k + 10) (a + 2) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 4⟩) (by execute fm 17)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 4 ∧ e % 2 = 0 ∧ a ≥ e)
  · intro c ⟨a, e, hq, he4, heven, hae⟩; subst hq
    rcases (show e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 from by omega) with h3 | h3 | h3
    · obtain ⟨k, hk⟩ : ∃ k, e = 3 * k + 3 := by
        obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h3
        exact ⟨k - 1, by omega⟩
      obtain ⟨m, hm⟩ : ∃ m, a = m + 2 * k + 3 := ⟨a - 2 * k - 3, by omega⟩
      subst hk; subst hm
      exact ⟨⟨m + 6 * k + 8, 0, 0, 0, 3 * k + 5⟩,
        ⟨m + 6 * k + 8, 3 * k + 5, rfl, by omega, by omega, by omega⟩,
        trans_mod0⟩
    · obtain ⟨k, hk⟩ : ∃ k, e = 3 * k + 4 := by exact ⟨e / 3 - 1, by omega⟩
      obtain ⟨m, hm⟩ : ∃ m, a = m + 2 * k + 4 := ⟨a - 2 * k - 4, by omega⟩
      subst hk; subst hm
      exact ⟨⟨m + 6 * k + 11, 0, 0, 0, 3 * k + 6⟩,
        ⟨m + 6 * k + 11, 3 * k + 6, rfl, by omega, by omega, by omega⟩,
        trans_mod1⟩
    · obtain ⟨k, hk⟩ : ∃ k, e = 3 * k + 8 := by exact ⟨e / 3 - 2, by omega⟩
      obtain ⟨m, hm⟩ : ∃ m, a = m + 2 * k + 8 := ⟨a - 2 * k - 8, by omega⟩
      subst hk; subst hm
      exact ⟨⟨m + 6 * k + 22, 0, 0, 0, 3 * k + 12⟩,
        ⟨m + 6 * k + 22, 3 * k + 12, rfl, by omega, by omega, by omega⟩,
        trans_mod2⟩
  · exact ⟨5, 4, rfl, by omega, by omega, by omega⟩
