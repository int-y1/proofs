import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz21_140_unofficial #132: [9/10, 77/2, 4/21, 5/7, 14/11]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  1  1
 2 -1  0 -1  0
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_132

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem d_to_c : ∀ k, ∀ c d e, (⟨0, 0, c, d+k, e⟩ : Q) [fm]⊢* ⟨0, 0, c+k, d, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

theorem five_step_round : ∀ b c e, (⟨0, b, c+3, 0, e+1⟩ : Q) [fm]⊢* ⟨0, b+5, c, 0, e⟩ := by
  intro b c e
  step fm; step fm; step fm; step fm; step fm; finish

theorem five_step_rounds : ∀ k, ∀ b c e,
    (⟨0, b, c+3*k, 0, e+k⟩ : Q) [fm]⊢* ⟨0, b+5*k, c, 0, e⟩ := by
  intro k; induction' k with k h <;> intro b c e
  · exists 0
  rw [show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  apply stepStar_trans (five_step_round _ _ _)
  rw [show b + 5 * (k + 1) = (b + 5) + 5 * k from by ring]
  exact h _ _ _

theorem drain_b : ∀ k, ∀ d e, (⟨0, k, 0, d+1, e⟩ : Q) [fm]⊢* ⟨0, 0, 0, d+k+1, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro d e
  · exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm; step fm; step fm
  rw [show d + (k + 1) + 1 = (d + 1) + k + 1 from by ring,
      show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
  exact h _ _

-- (0, b, 0, 0, e+1) → R5 → R2 → drain → (0, 0, 0, b+2, 2*b+e+1)
theorem tail_r0 : ∀ b e, (⟨0, b, 0, 0, e+1⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, b+2, 2*b+e+1⟩ := by
  intro b e
  step fm; step fm
  have h := drain_b b 1 (e+1)
  rw [show 1 + b + 1 = b + 2 from by ring,
      show e + 1 + 2 * b = 2 * b + e + 1 from by ring] at h
  exact h

-- (0, b, 1, 0, e+1) → R5,R1,R3,R2,R2 → drain → (0, 0, 0, b+3, 2*b+e+4)
theorem tail_r1 : ∀ b e, (⟨0, b, 1, 0, e+1⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, b+3, 2*b+e+4⟩ := by
  intro b e
  step fm; step fm; step fm; step fm; step fm
  have h := drain_b (b+1) 1 (e+2)
  rw [show 1 + (b + 1) + 1 = b + 3 from by ring,
      show e + 2 + 2 * (b + 1) = 2 * b + e + 4 from by ring] at h
  exact h

-- (0, b, 2, 0, e+1) → R5,R1,R3,R1,R2,R3,R2,R2 → drain → (0, 0, 0, b+4, 2*b+e+7)
theorem tail_r2 : ∀ b e, (⟨0, b, 2, 0, e+1⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, b+4, 2*b+e+7⟩ := by
  intro b e
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  have h := drain_b (b+2) 1 (e+3)
  rw [show 1 + (b + 2) + 1 = b + 4 from by ring,
      show e + 3 + 2 * (b + 2) = 2 * b + e + 7 from by ring] at h
  exact h

theorem trans_r0 (m : ℕ) (e : ℕ) (he : e ≥ m + 1) :
    (⟨0, 0, 0, 3*m, e⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, 5*m+2, e+9*m⟩ := by
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le he
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3*m, 0, m+1+e'⟩)
  · have h := d_to_c (3*m) 0 0 (m+1+e')
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 5*m, 0, 0, e'+1⟩)
  · have h := five_step_rounds m 0 0 (1+e')
    simp only [Nat.zero_add] at h
    rw [show 1 + e' + m = m + 1 + e' from by ring,
        show (1 + e' : ℕ) = e' + 1 from by ring] at h
    exact h
  have h := tail_r0 (5*m) e'
  rw [show 2 * (5 * m) + e' + 1 = (m + 1 + e') + 9 * m from by ring] at h
  exact h

theorem trans_r1 (m : ℕ) (e : ℕ) (he : e ≥ m + 1) :
    (⟨0, 0, 0, 3*m+1, e⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, 5*m+3, e+9*m+3⟩ := by
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le he
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3*m+1, 0, m+1+e'⟩)
  · have h := d_to_c (3*m+1) 0 0 (m+1+e')
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 5*m, 1, 0, e'+1⟩)
  · have h := five_step_rounds m 0 1 (1+e')
    simp only [Nat.zero_add] at h
    rw [show 1 + 3 * m = 3 * m + 1 from by ring,
        show 1 + e' + m = m + 1 + e' from by ring,
        show (1 + e' : ℕ) = e' + 1 from by ring] at h
    exact h
  have h := tail_r1 (5*m) e'
  rw [show 2 * (5 * m) + e' + 4 = (m + 1 + e') + 9 * m + 3 from by ring] at h
  exact h

theorem trans_r2 (m : ℕ) (e : ℕ) (he : e ≥ m + 1) :
    (⟨0, 0, 0, 3*m+2, e⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, 5*m+4, e+9*m+6⟩ := by
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le he
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3*m+2, 0, m+1+e'⟩)
  · have h := d_to_c (3*m+2) 0 0 (m+1+e')
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 5*m, 2, 0, e'+1⟩)
  · have h := five_step_rounds m 0 2 (1+e')
    simp only [Nat.zero_add] at h
    rw [show 2 + 3 * m = 3 * m + 2 from by ring,
        show 1 + e' + m = m + 1 + e' from by ring,
        show (1 + e' : ℕ) = e' + 1 from by ring] at h
    exact h
  have h := tail_r2 (5*m) e'
  rw [show 2 * (5 * m) + e' + 7 = (m + 1 + e') + 9 * m + 6 from by ring] at h
  exact h

theorem main_trans : ∀ d e, d ≥ 1 → e ≥ d →
    ∃ d' e', d' ≥ 1 ∧ e' ≥ d' ∧ (⟨0, 0, 0, d, e⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, d', e'⟩ := by
  intro d e hd hde
  have hmod := Nat.div_add_mod d 3
  set q := d / 3
  set r := d % 3
  have hr : r < 3 := Nat.mod_lt d (by omega)
  have he_bound : e ≥ q + 1 := by omega
  interval_cases r
  · have hq_pos : q ≥ 1 := by omega
    rw [show d = 3 * q from by omega]
    exact ⟨5*q+2, e+9*q, by omega, by omega, trans_r0 q e he_bound⟩
  · rw [show d = 3 * q + 1 from by omega]
    exact ⟨5*q+3, e+9*q+3, by omega, by omega, trans_r1 q e he_bound⟩
  · rw [show d = 3 * q + 2 from by omega]
    exact ⟨5*q+4, e+9*q+6, by omega, by omega, trans_r2 q e he_bound⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ e ≥ d)
  · intro c ⟨d, e, hq, hd, hde⟩
    subst hq
    obtain ⟨d', e', hd', hde', htrans⟩ := main_trans d e hd hde
    exact ⟨⟨0, 0, 0, d', e'⟩, ⟨d', e', rfl, hd', hde'⟩, htrans⟩
  · exact ⟨1, 1, rfl, by omega, by omega⟩

end Sz21_140_unofficial_132
