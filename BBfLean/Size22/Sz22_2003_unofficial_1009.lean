import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1009: [4/15, 9/14, 275/2, 7/5, 10/11]

Vector representation:
```
 2 -1 -1  0  0
-1  2  0 -1  0
-1  0  2  0  1
 0  0 -1  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1009

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ c e, (⟨k, 0, c, 0, e⟩ : Q) [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    step fm
    apply stepStar_trans (ih (c + 2) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ d e, (⟨0, 0, k, d, e⟩ : Q) [fm]⊢* ⟨0, 0, 0, d + k, e⟩ := by
  intro k; induction k with
  | zero => intro d e; exists 0
  | succ k ih =>
    intro d e
    step fm
    apply stepStar_trans (ih (d + 1) e)
    ring_nf; finish

theorem first_sub : ∀ D E, (⟨1, 0, 1, D + 3, E⟩ : Q) [fm]⊢* ⟨0, 5, 0, D, E⟩ := by
  intro D E
  step fm; step fm; step fm; step fm
  ring_nf; finish

theorem macro_chain : ∀ k, ∀ B D E,
    (⟨0, B + 1, 0, D + 3 * k, E + k⟩ : Q) [fm]⊢* ⟨0, B + 1 + 5 * k, 0, D, E⟩ := by
  intro k; induction k with
  | zero => intro B D E; ring_nf; finish
  | succ k ih =>
    intro B D E
    rw [show D + 3 * (k + 1) = (D + 3 * k) + 3 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (B + 5) D E)
    ring_nf; finish

theorem terminal_r2 : ∀ B E, (⟨0, B + 1, 0, 2, E + 1⟩ : Q) [fm]⊢* ⟨4, B + 2, 0, 0, E + 1⟩ := by
  intro B E
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem b_drain_even : ∀ k, ∀ a e,
    (⟨a + 1, 2 * k, 0, 0, e⟩ : Q) [fm]⊢* ⟨a + 1 + 3 * k, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; ring_nf; finish
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (e + 1))
    ring_nf; finish

theorem b_drain_odd : ∀ k, ∀ a e,
    (⟨a + 1, 2 * k + 1, 0, 0, e⟩ : Q) [fm]⊢* ⟨a + 3 * k + 2, 0, 1, 0, e + k + 1⟩ := by
  intro k; induction k with
  | zero =>
    intro a e; step fm; step fm
    ring_nf; finish
  | succ k ih =>
    intro a e
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (e + 1))
    ring_nf; finish

theorem trans_type1 (m : ℕ) (hm : m ≥ 1) (E : ℕ) :
    (⟨3 * m + 1, 0, 0, 0, E⟩ : Q) [fm]⊢⁺ ⟨15 * m + 5, 0, 1, 0, E + 6 * m + 2⟩ := by
  have h1 : (⟨3 * m + 1, 0, 0, 0, E⟩ : Q) [fm]⊢⁺ ⟨0, 0, 6 * m + 2, 0, E + 3 * m + 1⟩ := by
    rw [show 3 * m + 1 = (3 * m) + 1 from by ring]
    step fm
    apply stepStar_trans (r3_chain (3 * m) 2 (E + 1))
    rw [show 2 + 2 * (3 * m) = 6 * m + 2 from by ring,
        show E + 1 + 3 * m = E + 3 * m + 1 from by ring]
    finish
  have h2 : (⟨0, 0, 6 * m + 2, 0, E + 3 * m + 1⟩ : Q) [fm]⊢* ⟨0, 0, 0, 6 * m + 2, E + 3 * m + 1⟩ := by
    have := r4_chain (6 * m + 2) 0 (E + 3 * m + 1)
    rw [show 0 + (6 * m + 2) = 6 * m + 2 from by ring] at this; exact this
  have h3 : (⟨0, 0, 0, 6 * m + 2, E + 3 * m + 1⟩ : Q) [fm]⊢* ⟨0, 5, 0, 6 * m - 1, E + 3 * m⟩ := by
    rw [show 6 * m + 2 = (6 * m + 2) from rfl,
        show E + 3 * m + 1 = (E + 3 * m) + 1 from by ring]
    step fm
    rw [show 6 * m + 1 + 1 = (6 * m - 1) + 3 from by omega]
    exact first_sub (6 * m - 1) (E + 3 * m)
  have h456 : (⟨0, 5, 0, 6 * m - 1, E + 3 * m⟩ : Q) [fm]⊢* ⟨15 * m + 5, 0, 1, 0, E + 6 * m + 2⟩ := by
    rw [show (5 : ℕ) = 4 + 1 from rfl,
        show 6 * m - 1 = 2 + 3 * (2 * m - 1) from by omega,
        show E + 3 * m = E + m + 1 + (2 * m - 1) from by omega]
    apply stepStar_trans (macro_chain (2 * m - 1) 4 2 (E + m + 1))
    rw [show 4 + 1 + 5 * (2 * m - 1) = (10 * m - 1) + 1 from by omega,
        show E + m + 1 = (E + m) + 1 from by ring]
    apply stepStar_trans (terminal_r2 (10 * m - 1) (E + m))
    rw [show (4 : ℕ) = 3 + 1 from rfl,
        show 10 * m - 1 + 2 = 2 * (5 * m) + 1 from by omega,
        show E + m + 1 = E + m + 1 from rfl]
    apply stepStar_trans (b_drain_odd (5 * m) 3 (E + m + 1))
    rw [show 3 + 3 * (5 * m) + 2 = 15 * m + 5 from by ring,
        show E + m + 1 + 5 * m + 1 = E + 6 * m + 2 from by ring]
    finish
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 h456))

theorem trans_type2 (m : ℕ) (E : ℕ) :
    (⟨3 * m + 2, 0, 1, 0, E⟩ : Q) [fm]⊢⁺ ⟨15 * m + 13, 0, 0, 0, E + 6 * m + 4⟩ := by
  have h1 : (⟨3 * m + 2, 0, 1, 0, E⟩ : Q) [fm]⊢⁺ ⟨0, 0, 6 * m + 5, 0, E + 3 * m + 2⟩ := by
    rw [show 3 * m + 2 = (3 * m + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (r3_chain (3 * m + 1) 3 (E + 1))
    rw [show 3 + 2 * (3 * m + 1) = 6 * m + 5 from by ring,
        show E + 1 + (3 * m + 1) = E + 3 * m + 2 from by ring]
    finish
  have h2 : (⟨0, 0, 6 * m + 5, 0, E + 3 * m + 2⟩ : Q) [fm]⊢* ⟨0, 0, 0, 6 * m + 5, E + 3 * m + 2⟩ := by
    have := r4_chain (6 * m + 5) 0 (E + 3 * m + 2)
    rw [show 0 + (6 * m + 5) = 6 * m + 5 from by ring] at this; exact this
  have h3 : (⟨0, 0, 0, 6 * m + 5, E + 3 * m + 2⟩ : Q) [fm]⊢* ⟨0, 5, 0, 6 * m + 2, E + 3 * m + 1⟩ := by
    rw [show E + 3 * m + 2 = (E + 3 * m + 1) + 1 from by ring]
    step fm
    rw [show 6 * m + 4 + 1 = (6 * m + 2) + 3 from by ring]
    exact first_sub (6 * m + 2) (E + 3 * m + 1)
  have h4 : (⟨0, 5, 0, 6 * m + 2, E + 3 * m + 1⟩ : Q) [fm]⊢* ⟨0, 10 * m + 5, 0, 2, E + m + 1⟩ := by
    rw [show (5 : ℕ) = 4 + 1 from rfl,
        show 6 * m + 2 = 2 + 3 * (2 * m) from by ring,
        show E + 3 * m + 1 = E + m + 1 + 2 * m from by ring]
    have := macro_chain (2 * m) 4 2 (E + m + 1)
    rw [show 4 + 1 + 5 * (2 * m) = 10 * m + 5 from by ring] at this; exact this
  have h5 : (⟨0, 10 * m + 5, 0, 2, E + m + 1⟩ : Q) [fm]⊢* ⟨4, 10 * m + 6, 0, 0, E + m + 1⟩ := by
    rw [show (10 * m + 5 : ℕ) = (10 * m + 4) + 1 from by ring,
        show E + m + 1 = (E + m) + 1 from by ring]
    have := terminal_r2 (10 * m + 4) (E + m)
    rw [show 10 * m + 4 + 2 = 10 * m + 6 from by ring,
        show E + m + 1 = E + m + 1 from rfl] at this; exact this
  have h6 : (⟨4, 10 * m + 6, 0, 0, E + m + 1⟩ : Q) [fm]⊢* ⟨15 * m + 13, 0, 0, 0, E + 6 * m + 4⟩ := by
    rw [show (4 : ℕ) = 3 + 1 from rfl,
        show 10 * m + 6 = 2 * (5 * m + 3) from by ring]
    have := b_drain_even (5 * m + 3) 3 (E + m + 1)
    rw [show 3 + 1 + 3 * (5 * m + 3) = 15 * m + 13 from by ring,
        show E + m + 1 + (5 * m + 3) = E + 6 * m + 4 from by ring] at this; exact this
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 1, 0, 2⟩) (by execute fm 12)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m e, m ≥ 1 ∧ e ≥ 2 ∧
      (q = ⟨3 * m + 1, 0, 0, 0, e⟩ ∨ q = ⟨3 * m + 2, 0, 1, 0, e⟩))
  · intro q ⟨m, e, hm, he, hq⟩
    rcases hq with rfl | rfl
    · exact ⟨⟨15 * m + 5, 0, 1, 0, e + 6 * m + 2⟩,
        ⟨5 * m + 1, e + 6 * m + 2,
         by omega, by omega,
         Or.inr (by ring_nf)⟩,
        trans_type1 m hm e⟩
    · exact ⟨⟨15 * m + 13, 0, 0, 0, e + 6 * m + 4⟩,
        ⟨5 * m + 4, e + 6 * m + 4,
         by omega, by omega,
         Or.inl (by ring_nf)⟩,
        trans_type2 m e⟩
  · exact ⟨1, 2, by omega, by omega, Or.inr rfl⟩

end Sz22_2003_unofficial_1009
