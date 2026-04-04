import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1866: [9/35, 25/33, 14/3, 11/7, 147/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  2  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1866

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

theorem d_to_e : ∀ k d, ⟨a, 0, 0, d + k, 0⟩ [fm]⊢* ⟨a, 0, 0, d, k⟩ := by
  intro k; induction k with
  | zero => intro d; exists 0
  | succ k ih =>
    intro d; rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (d + 1))
    step fm; ring_nf; finish

theorem b_to_ad : ∀ k a b, ⟨a, b + k, 0, 0, 0⟩ [fm]⊢* ⟨a + k, b, 0, k, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; exists 0
  | succ k ih =>
    intro a b; rw [show b + (k + 1) = (b + 1) + k from by ring]
    apply stepStar_trans (ih a (b + 1))
    step fm; ring_nf; finish

theorem spiral : ∀ n a b, ⟨a, b, n + 1, 1, 0⟩ [fm]⊢* ⟨a + n, b + n + 2, 0, 0, 0⟩ := by
  intro n; induction n with
  | zero => intro a b; step fm; finish
  | succ n ih =>
    intro a b; step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 1))
    ring_nf; finish

theorem round_C0 : ⟨a + 1, 0, 0, 0, e + 5⟩ [fm]⊢* ⟨a, 0, 8, 0, e⟩ := by
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; ring_nf; finish

theorem round_Cge2 : ⟨a + 1, 0, c + 2, 0, e + 5⟩ [fm]⊢* ⟨a, 0, c + 10, 0, e⟩ := by
  step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm; ring_nf; finish

theorem multi_round : ∀ k r a, ⟨a + k + 1, 0, 0, 0, 5 * (k + 1) + r⟩ [fm]⊢*
    ⟨a, 0, 8 * (k + 1), 0, r⟩ := by
  intro k; induction k with
  | zero =>
    intro r a; rw [show 5 * (0 + 1) + r = r + 5 from by ring,
      show 8 * (0 + 1) = 8 from by ring, show a + 0 + 1 = a + 1 from by ring]
    exact round_C0
  | succ k ih =>
    intro r a; rw [show a + (k + 1) + 1 = (a + 1) + k + 1 from by ring,
      show 5 * (k + 1 + 1) + r = 5 * (k + 1) + (r + 5) from by ring]
    apply stepStar_trans (ih (r + 5) (a + 1))
    rw [show 8 * (k + 1) = (8 * k + 6) + 2 from by ring]
    apply stepStar_trans (round_Cge2 (a := a) (c := 8 * k + 6) (e := r))
    ring_nf; finish

theorem finish_r0 : ⟨a + 1, 0, c + 2, 0, 0⟩ [fm]⊢⁺ ⟨a + c, c + 5, 0, 0, 0⟩ := by
  step fm; step fm; step fm
  show ⟨a, 5, c, 0, 0⟩ [fm]⊢* ⟨a + c, c + 5, 0, 0, 0⟩
  rcases c with _ | c; · finish
  step fm
  show ⟨a + 1, 4, c + 1, 1, 0⟩ [fm]⊢* ⟨a + (c + 1), (c + 1) + 5, 0, 0, 0⟩
  apply stepStar_trans (spiral c (a + 1) 4); ring_nf; finish

theorem finish_r1 : ⟨a + 1, 0, c + 2, 0, 1⟩ [fm]⊢⁺ ⟨a + c + 2, c + 6, 0, 0, 0⟩ := by
  step fm; step fm; step fm; step fm
  show ⟨a, 4, c + 2, 0, 0⟩ [fm]⊢* ⟨a + c + 2, c + 6, 0, 0, 0⟩
  step fm; step fm; step fm
  show ⟨a + 2, 4, c + 1, 1, 0⟩ [fm]⊢* ⟨a + c + 2, c + 6, 0, 0, 0⟩
  apply stepStar_trans (spiral c (a + 2) 4); ring_nf; finish

theorem finish_r2 : ⟨a + 1, 0, c + 2, 0, 2⟩ [fm]⊢⁺ ⟨a + c + 4, c + 7, 0, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm
  show ⟨a, 3, c + 4, 0, 0⟩ [fm]⊢* ⟨a + c + 4, c + 7, 0, 0, 0⟩
  step fm; step fm; step fm
  show ⟨a + 2, 3, c + 3, 1, 0⟩ [fm]⊢* ⟨a + c + 4, c + 7, 0, 0, 0⟩
  apply stepStar_trans (spiral (c + 2) (a + 2) 3); ring_nf; finish

theorem finish_r3 : ⟨a + 1, 0, c + 2, 0, 3⟩ [fm]⊢⁺ ⟨a + c + 6, c + 8, 0, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨a, 2, c + 6, 0, 0⟩ [fm]⊢* ⟨a + c + 6, c + 8, 0, 0, 0⟩
  step fm; step fm; step fm
  show ⟨a + 2, 2, c + 5, 1, 0⟩ [fm]⊢* ⟨a + c + 6, c + 8, 0, 0, 0⟩
  apply stepStar_trans (spiral (c + 4) (a + 2) 2); ring_nf; finish

theorem finish_r4 : ⟨a + 1, 0, c + 2, 0, 4⟩ [fm]⊢⁺ ⟨a + c + 8, c + 9, 0, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨a, 1, c + 8, 0, 0⟩ [fm]⊢* ⟨a + c + 8, c + 9, 0, 0, 0⟩
  step fm; step fm; step fm
  show ⟨a + 2, 1, c + 7, 1, 0⟩ [fm]⊢* ⟨a + c + 8, c + 9, 0, 0, 0⟩
  apply stepStar_trans (spiral (c + 6) (a + 2) 1); ring_nf; finish

theorem macro_e1 : ⟨a + 1, 0, 0, 0, 1⟩ [fm]⊢⁺ ⟨a, 4, 0, 0, 0⟩ := by execute fm 4
theorem macro_e2 : ⟨a + 1, 0, 0, 0, 2⟩ [fm]⊢⁺ ⟨a + 2, 5, 0, 0, 0⟩ := by execute fm 9
theorem macro_e3 : ⟨a + 1, 0, 0, 0, 3⟩ [fm]⊢⁺ ⟨a + 4, 6, 0, 0, 0⟩ := by execute fm 14
theorem macro_e4 : ⟨a + 1, 0, 0, 0, 4⟩ [fm]⊢⁺ ⟨a + 6, 7, 0, 0, 0⟩ := by execute fm 19

theorem macro_mod0 : ∀ k, ⟨a + k + 2, 0, 0, 0, 5 * (k + 1)⟩ [fm]⊢⁺
    ⟨a + 8 * k + 6, 8 * k + 11, 0, 0, 0⟩ := by
  intro k
  rw [show 5 * (k + 1) = 5 * (k + 1) + 0 from by ring,
      show a + k + 2 = (a + 1) + k + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (multi_round k (a + 1) (r := 0))
  rw [show 8 * (k + 1) = (8 * k + 6) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (finish_r0 (a := a) (c := 8 * k + 6))
  ring_nf; finish

theorem macro_mod1 : ∀ k, ⟨a + k + 2, 0, 0, 0, 5 * (k + 1) + 1⟩ [fm]⊢⁺
    ⟨a + 8 * k + 8, 8 * k + 12, 0, 0, 0⟩ := by
  intro k
  rw [show a + k + 2 = (a + 1) + k + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (multi_round k (a + 1) (r := 1))
  rw [show 8 * (k + 1) = (8 * k + 6) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (finish_r1 (a := a) (c := 8 * k + 6))
  ring_nf; finish

theorem macro_mod2 : ∀ k, ⟨a + k + 2, 0, 0, 0, 5 * (k + 1) + 2⟩ [fm]⊢⁺
    ⟨a + 8 * k + 10, 8 * k + 13, 0, 0, 0⟩ := by
  intro k
  rw [show a + k + 2 = (a + 1) + k + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (multi_round k (a + 1) (r := 2))
  rw [show 8 * (k + 1) = (8 * k + 6) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (finish_r2 (a := a) (c := 8 * k + 6))
  ring_nf; finish

theorem macro_mod3 : ∀ k, ⟨a + k + 2, 0, 0, 0, 5 * (k + 1) + 3⟩ [fm]⊢⁺
    ⟨a + 8 * k + 12, 8 * k + 14, 0, 0, 0⟩ := by
  intro k
  rw [show a + k + 2 = (a + 1) + k + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (multi_round k (a + 1) (r := 3))
  rw [show 8 * (k + 1) = (8 * k + 6) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (finish_r3 (a := a) (c := 8 * k + 6))
  ring_nf; finish

theorem macro_mod4 : ∀ k, ⟨a + k + 2, 0, 0, 0, 5 * (k + 1) + 4⟩ [fm]⊢⁺
    ⟨a + 8 * k + 14, 8 * k + 15, 0, 0, 0⟩ := by
  intro k
  rw [show a + k + 2 = (a + 1) + k + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (multi_round k (a + 1) (r := 4))
  rw [show 8 * (k + 1) = (8 * k + 6) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (finish_r4 (a := a) (c := 8 * k + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 6, 0, 0, 0⟩) (by execute fm 19)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A B, q = ⟨A, B, 0, 0, 0⟩ ∧ A ≥ 1 ∧ B ≥ 4)
  · intro c ⟨A, B, hq, hA, hB⟩; subst hq
    obtain ⟨m, rfl⟩ : ∃ m, A = m + 1 := ⟨A - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, B = b + 4 := ⟨B - 4, by omega⟩
    obtain ⟨q, rfl | rfl | rfl | rfl | rfl⟩ : ∃ q, b = 5 * q ∨ b = 5 * q + 1 ∨
        b = 5 * q + 2 ∨ b = 5 * q + 3 ∨ b = 5 * q + 4 := ⟨b / 5, by omega⟩
    · -- B = 5*q + 4
      rcases q with _ | q
      · -- B=4
        refine ⟨⟨m + 10, 7, 0, 0, 0⟩, ⟨m + 10, 7, rfl, by omega, by omega⟩, ?_⟩
        show ⟨m + 1, 5 * 0 + 4, 0, 0, 0⟩ [fm]⊢⁺ ⟨m + 10, 7, 0, 0, 0⟩
        rw [show (5 * 0 + 4 : ℕ) = 0 + 4 from by ring]
        apply stepStar_stepPlus_stepPlus (b_to_ad 4 (m + 1) 0)
        rw [show (4 : ℕ) = 0 + 4 from by ring]
        apply stepStar_stepPlus_stepPlus (d_to_e 4 0 (a := m + 5))
        rw [show m + 5 = (m + 4) + 1 from by ring]
        exact macro_e4 (a := m + 4)
      · -- B = 5*(q+1)+4
        refine ⟨⟨m + 12 * q + 22, 8 * q + 15, 0, 0, 0⟩,
          ⟨m + 12 * q + 22, 8 * q + 15, rfl, by omega, by omega⟩, ?_⟩
        show ⟨m + 1, 5 * (q + 1) + 4, 0, 0, 0⟩ [fm]⊢⁺ _
        rw [show (5 * (q + 1) + 4 : ℕ) = 0 + (5 * (q + 1) + 4) from by ring]
        apply stepStar_stepPlus_stepPlus (b_to_ad (5 * (q + 1) + 4) (m + 1) 0)
        rw [show m + 1 + (5 * (q + 1) + 4) = m + 5 * q + 10 from by ring,
            show (5 * (q + 1) + 4 : ℕ) = 0 + (5 * (q + 1) + 4) from by ring]
        apply stepStar_stepPlus_stepPlus (d_to_e (5 * (q + 1) + 4) 0 (a := m + 5 * q + 10))
        rw [show m + 5 * q + 10 = (m + 4 * q + 8) + q + 2 from by ring,
            show 5 * (q + 1) + 4 = 5 * (q + 1) + 4 from rfl]
        apply stepPlus_stepStar_stepPlus (macro_mod4 q (a := m + 4 * q + 8))
        ring_nf; finish
    · -- B = 5*q + 5
      refine ⟨⟨m + 12 * q + 10, 8 * q + 11, 0, 0, 0⟩,
        ⟨m + 12 * q + 10, 8 * q + 11, rfl, by omega, by omega⟩, ?_⟩
      show ⟨m + 1, 5 * q + 1 + 4, 0, 0, 0⟩ [fm]⊢⁺ _
      rw [show (5 * q + 1 + 4 : ℕ) = 0 + (5 * q + 5) from by ring]
      apply stepStar_stepPlus_stepPlus (b_to_ad (5 * q + 5) (m + 1) 0)
      rw [show m + 1 + (5 * q + 5) = m + 5 * q + 6 from by ring,
          show (5 * q + 5 : ℕ) = 0 + (5 * q + 5) from by ring]
      apply stepStar_stepPlus_stepPlus (d_to_e (5 * q + 5) 0 (a := m + 5 * q + 6))
      rw [show m + 5 * q + 6 = (m + 4 * q + 4) + q + 2 from by ring,
          show 5 * q + 5 = 5 * (q + 1) from by ring]
      apply stepPlus_stepStar_stepPlus (macro_mod0 q (a := m + 4 * q + 4))
      ring_nf; finish
    · -- B = 5*q + 6
      refine ⟨⟨m + 12 * q + 13, 8 * q + 12, 0, 0, 0⟩,
        ⟨m + 12 * q + 13, 8 * q + 12, rfl, by omega, by omega⟩, ?_⟩
      show ⟨m + 1, 5 * q + 2 + 4, 0, 0, 0⟩ [fm]⊢⁺ _
      rw [show (5 * q + 2 + 4 : ℕ) = 0 + (5 * q + 6) from by ring]
      apply stepStar_stepPlus_stepPlus (b_to_ad (5 * q + 6) (m + 1) 0)
      rw [show m + 1 + (5 * q + 6) = m + 5 * q + 7 from by ring,
          show (5 * q + 6 : ℕ) = 0 + (5 * q + 6) from by ring]
      apply stepStar_stepPlus_stepPlus (d_to_e (5 * q + 6) 0 (a := m + 5 * q + 7))
      rw [show m + 5 * q + 7 = (m + 4 * q + 5) + q + 2 from by ring,
          show 5 * q + 6 = 5 * (q + 1) + 1 from by ring]
      apply stepPlus_stepStar_stepPlus (macro_mod1 q (a := m + 4 * q + 5))
      ring_nf; finish
    · -- B = 5*q + 7
      refine ⟨⟨m + 12 * q + 16, 8 * q + 13, 0, 0, 0⟩,
        ⟨m + 12 * q + 16, 8 * q + 13, rfl, by omega, by omega⟩, ?_⟩
      show ⟨m + 1, 5 * q + 3 + 4, 0, 0, 0⟩ [fm]⊢⁺ _
      rw [show (5 * q + 3 + 4 : ℕ) = 0 + (5 * q + 7) from by ring]
      apply stepStar_stepPlus_stepPlus (b_to_ad (5 * q + 7) (m + 1) 0)
      rw [show m + 1 + (5 * q + 7) = m + 5 * q + 8 from by ring,
          show (5 * q + 7 : ℕ) = 0 + (5 * q + 7) from by ring]
      apply stepStar_stepPlus_stepPlus (d_to_e (5 * q + 7) 0 (a := m + 5 * q + 8))
      rw [show m + 5 * q + 8 = (m + 4 * q + 6) + q + 2 from by ring,
          show 5 * q + 7 = 5 * (q + 1) + 2 from by ring]
      apply stepPlus_stepStar_stepPlus (macro_mod2 q (a := m + 4 * q + 6))
      ring_nf; finish
    · -- B = 5*q + 8
      refine ⟨⟨m + 12 * q + 19, 8 * q + 14, 0, 0, 0⟩,
        ⟨m + 12 * q + 19, 8 * q + 14, rfl, by omega, by omega⟩, ?_⟩
      show ⟨m + 1, 5 * q + 4 + 4, 0, 0, 0⟩ [fm]⊢⁺ _
      rw [show (5 * q + 4 + 4 : ℕ) = 0 + (5 * q + 8) from by ring]
      apply stepStar_stepPlus_stepPlus (b_to_ad (5 * q + 8) (m + 1) 0)
      rw [show m + 1 + (5 * q + 8) = m + 5 * q + 9 from by ring,
          show (5 * q + 8 : ℕ) = 0 + (5 * q + 8) from by ring]
      apply stepStar_stepPlus_stepPlus (d_to_e (5 * q + 8) 0 (a := m + 5 * q + 9))
      rw [show m + 5 * q + 9 = (m + 4 * q + 7) + q + 2 from by ring,
          show 5 * q + 8 = 5 * (q + 1) + 3 from by ring]
      apply stepPlus_stepStar_stepPlus (macro_mod3 q (a := m + 4 * q + 7))
      ring_nf; finish
  · exact ⟨4, 6, rfl, by omega, by omega⟩
