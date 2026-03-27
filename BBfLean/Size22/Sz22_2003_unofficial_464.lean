import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #464: [28/15, 21/22, 175/2, 11/7, 3/11]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  1 -1
-1  0  2  1  0
 0  0  0 -1  1
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_464

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem d_to_e : ∀ k c d e, (⟨0, 0, c, d + k, e⟩ : Q) [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro c d e; rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem a_to_c : ∀ k a c d, (⟨a + k, 0, c, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, c + 2 * k, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro a c d; rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem r1r2_chain : ∀ k j c D e,
    (⟨j, 1, c + k, D, e + k⟩ : Q) [fm]⊢* ⟨j + k, 1, c, D + 2 * k, e⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro j c D e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; rw [show (e + k) + 1 = e + (k + 1) from by ring]; step fm
    apply stepStar_trans (ih _ _ _ _); ring_nf; finish

theorem r2_chain : ∀ k a b D,
    (⟨a + k, b, 0, D, k⟩ : Q) [fm]⊢* ⟨a, b + k, 0, D + k, 0⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro a b D
    rw [show a + (k + 1) = (a + k) + 1 from by ring, show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem bounce_even : ∀ k a D,
    (⟨a + 1, 2 * k, 0, D, 0⟩ : Q) [fm]⊢* ⟨a + 3 * k + 1, 0, 0, D + 3 * k, 0⟩ := by
  intro k; induction k with
  | zero => intros; exists 0
  | succ k ih =>
    intro a D; rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

theorem bounce_odd : ∀ k a D,
    (⟨a + 1, 2 * k + 1, 0, D, 0⟩ : Q) [fm]⊢* ⟨a + 3 * k + 2, 0, 1, D + 3 * k + 2, 0⟩ := by
  intro k; induction k with
  | zero => intro a D; step fm; step fm; finish
  | succ k ih =>
    intro a D; rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish

-- Case 1: c >= d >= 1. Write c = d + r, d = d' + 1.
-- (0, 0, d'+1+r, d'+1, 0) ⊢⁺ (0, 0, r+2*d'+4, 3*d'+3, 0)
theorem trans_ge (r d' : ℕ) :
    (⟨0, 0, d' + 1 + r, d' + 1, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, r + 2 * d' + 4, 3 * d' + 3, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, d' + 1 + r, 0, d' + 1⟩)
  · have h := d_to_e (d' + 1) (d' + 1 + r) 0 0; simp only [Nat.zero_add] at h; exact h
  step fm
  apply stepStar_trans (c₂ := ⟨d', 1, r + 1, 2 * d', 0⟩)
  · have h := r1r2_chain d' 0 (r + 1) 0 0; simp only [Nat.zero_add] at h
    rw [show r + 1 + d' = d' + 1 + r from by ring] at h; exact h
  step fm
  have h := a_to_c (d' + 2) 0 r (2 * d' + 1); simp only [Nat.zero_add] at h
  rw [show r + 2 * (d' + 2) = r + 2 * d' + 4 from by ring,
      show 2 * d' + 1 + (d' + 2) = 3 * d' + 3 from by ring] at h; exact h

-- Case 2: d > c, d - c = 2*k+1 (odd), c = c'+1, c' >= 2*k+3.
-- R4 drain -> R5 -> R1/R2 chain c' rounds -> R1 -> R2 drain -> bounce_odd -> R3 drain
theorem trans_lt_odd (c' k : ℕ) (hc' : c' ≥ 2 * k + 3) :
    (⟨0, 0, c' + 1, c' + 2 * k + 2, 0⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 2 * c' + 2 * k + 5, 3 * c' + 6 * k + 6, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, c' + 1, 0, c' + 2 * k + 2⟩)
  · have h := d_to_e (c' + 2 * k + 2) (c' + 1) 0 0; simp only [Nat.zero_add] at h; exact h
  step fm
  apply stepStar_trans (c₂ := ⟨c', 1, 1, 2 * c', 2 * k + 1⟩)
  · have h := r1r2_chain c' 0 1 0 (2 * k + 1)
    simp only [Nat.zero_add] at h
    rw [show 1 + c' = c' + 1 from by ring,
        show 2 * k + 1 + c' = c' + 2 * k + 1 from by ring] at h; exact h
  step fm
  apply stepStar_trans (c₂ := ⟨c' - 2 * k + 1, 2 * k + 1, 0, 2 * c' + 2 * k + 2, 0⟩)
  · have h := r2_chain (2 * k + 1) (c' - 2 * k + 1) 0 (2 * c' + 1)
    rw [show c' - 2 * k + 1 + (2 * k + 1) = c' + 2 from by omega,
        show 0 + (2 * k + 1) = 2 * k + 1 from by ring,
        show 2 * c' + 1 + (2 * k + 1) = 2 * c' + 2 * k + 2 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨c' + k + 2, 0, 1, 2 * c' + 5 * k + 4, 0⟩)
  · have h := bounce_odd k (c' - 2 * k) (2 * c' + 2 * k + 2)
    rw [show c' - 2 * k + 1 = (c' - 2 * k) + 1 from by omega,
        show (c' - 2 * k) + 3 * k + 2 = c' + k + 2 from by omega,
        show 2 * c' + 2 * k + 2 + 3 * k + 2 = 2 * c' + 5 * k + 4 from by ring] at h; exact h
  have h := a_to_c (c' + k + 2) 0 1 (2 * c' + 5 * k + 4)
  simp only [Nat.zero_add] at h
  rw [show 1 + 2 * (c' + k + 2) = 2 * c' + 2 * k + 5 from by ring,
      show 2 * c' + 5 * k + 4 + (c' + k + 2) = 3 * c' + 6 * k + 6 from by ring] at h
  exact h

-- Case 3: d > c, d - c = 2*(k+1) (even >= 2), c = c'+1, c' >= 2*k+4.
-- R4 drain -> R5 -> R1/R2 chain c' rounds -> R1 -> R2 drain -> bounce_even -> R3 drain
theorem trans_lt_even (c' k : ℕ) (hc' : c' ≥ 2 * k + 4) :
    (⟨0, 0, c' + 1, c' + 2 * k + 3, 0⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 2 * c' + 2 * k + 6, 3 * c' + 6 * k + 9, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, c' + 1, 0, c' + 2 * k + 3⟩)
  · have h := d_to_e (c' + 2 * k + 3) (c' + 1) 0 0; simp only [Nat.zero_add] at h; exact h
  step fm
  apply stepStar_trans (c₂ := ⟨c', 1, 1, 2 * c', 2 * k + 2⟩)
  · have h := r1r2_chain c' 0 1 0 (2 * k + 2)
    simp only [Nat.zero_add] at h
    rw [show 1 + c' = c' + 1 from by ring,
        show 2 * k + 2 + c' = c' + 2 * k + 2 from by ring] at h; exact h
  step fm
  apply stepStar_trans (c₂ := ⟨c' - 2 * k, 2 * k + 2, 0, 2 * c' + 2 * k + 3, 0⟩)
  · have h := r2_chain (2 * k + 2) (c' - 2 * k) 0 (2 * c' + 1)
    rw [show c' - 2 * k + (2 * k + 2) = c' + 2 from by omega,
        show 0 + (2 * k + 2) = 2 * k + 2 from by ring,
        show 2 * c' + 1 + (2 * k + 2) = 2 * c' + 2 * k + 3 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨c' + k + 3, 0, 0, 2 * c' + 5 * k + 6, 0⟩)
  · have h := bounce_even (k + 1) (c' - 2 * k - 1) (2 * c' + 2 * k + 3)
    rw [show c' - 2 * k - 1 + 1 = c' - 2 * k from by omega,
        show 2 * (k + 1) = 2 * k + 2 from by ring,
        show c' - 2 * k - 1 + 3 * (k + 1) + 1 = c' + k + 3 from by omega,
        show 2 * c' + 2 * k + 3 + 3 * (k + 1) = 2 * c' + 5 * k + 6 from by ring] at h; exact h
  have h := a_to_c (c' + k + 3) 0 0 (2 * c' + 5 * k + 6)
  simp only [Nat.zero_add] at h
  rw [show 2 * (c' + k + 3) = 2 * c' + 2 * k + 6 from by ring,
      show 2 * c' + 5 * k + 6 + (c' + k + 3) = 3 * c' + 6 * k + 9 from by ring] at h
  exact h

theorem main_trans (c d : ℕ) (hd : d ≥ 1) (hinv : 2 * c ≥ d + 3) :
    ∃ c' d', 2 * c' ≥ d' + 3 ∧ d' ≥ 1 ∧
    (⟨0, 0, c, d, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, c', d', 0⟩ := by
  refine ⟨c + d + 2, 3 * d, by omega, by omega, ?_⟩
  by_cases hcd : c ≥ d
  · -- Case 1: c >= d
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, c = d' + 1 + r := ⟨c - d' - 1, by omega⟩
    rw [show d' + 1 + r + (d' + 1) + 2 = r + 2 * d' + 4 from by ring,
        show 3 * (d' + 1) = 3 * d' + 3 from by ring]
    exact trans_ge r d'
  · -- Case 2/3: c < d
    push_neg at hcd
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hgap : d - c' - 1 ≥ 1 := by omega
    rcases Nat.even_or_odd (d - c' - 1) with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- d - c' - 1 even = 2*k, k >= 1 since d > c
      have hk1 : k ≥ 1 := by omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hd_eq : d = c' + 2 * k' + 3 := by omega
      rw [hd_eq]
      rw [show c' + 1 + (c' + 2 * k' + 3) + 2 = 2 * c' + 2 * k' + 6 from by ring,
          show 3 * (c' + 2 * k' + 3) = 3 * c' + 6 * k' + 9 from by ring]
      exact trans_lt_even c' k' (by omega)
    · -- d - c' - 1 odd = 2*k+1
      have hd_eq : d = c' + 2 * k + 2 := by omega
      rw [hd_eq]
      rw [show c' + 1 + (c' + 2 * k + 2) + 2 = 2 * c' + 2 * k + 5 from by ring,
          show 3 * (c' + 2 * k + 2) = 3 * c' + 6 * k + 6 from by ring]
      exact trans_lt_odd c' k (by omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c, d, 0⟩ ∧ d ≥ 1 ∧ 2 * c ≥ d + 3)
  · intro q ⟨c, d, hq, hd, hinv⟩
    subst hq
    obtain ⟨c', d', hinv', hd', htrans⟩ := main_trans c d hd hinv
    exact ⟨⟨0, 0, c', d', 0⟩, ⟨c', d', rfl, hd', hinv'⟩, htrans⟩
  · exact ⟨2, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_464
