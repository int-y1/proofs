import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #22: [1/135, 98/15, 63/2, 5/7, 3/5]

Vector representation:
```
 0 -3 -1  0
 1 -1 -1  2
-1  2  0  1
 0  0  1 -1
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_22

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+3, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+2⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+2, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4 transfer: d → c (a=0, b=0)
theorem d_to_c : ∀ k, ∀ c d, ⟨0, 0, c, d + k⟩ [fm]⊢* ⟨0, 0, c + k, d⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  have h := ih (c + 1) d
  rw [show c + 1 + k = c + (k + 1) from by ring] at h
  exact h

-- Climbing round: R3, R2, R2 (3 steps)
theorem climb_round : ∀ k, ∀ n c d, ⟨n + 1, 0, c + 2 * k, d⟩ [fm]⊢* ⟨n + 1 + k, 0, c, d + 5 * k⟩ := by
  intro k; induction' k with k ih <;> intro n c d
  · simp; exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (n + 1) c (d + 5))
  ring_nf; finish

-- Climbing for even c = 2*(k+1): (0, 0, 2*(k+1), 0) ⊢* (k+1, 0, 0, 5*k+2)
theorem climb_even (k : ℕ) : ⟨0, 0, 2 * (k + 1), 0⟩ [fm]⊢* ⟨k + 1, 0, 0, 5 * k + 2⟩ := by
  rw [show 2 * (k + 1) = 0 + 2 * k + 2 from by ring]
  step fm; step fm
  have h := climb_round k 0 0 2
  simp only [Nat.zero_add] at h ⊢
  rw [show 1 + k = k + 1 from by ring, show 2 + 5 * k = 5 * k + 2 from by ring] at h
  exact h

-- Climbing for odd c = 2*k+3: (0, 0, 2*k+3, 0) ⊢* (k+1, 0, 1, 5*k+2)
theorem climb_odd (k : ℕ) : ⟨0, 0, 2 * k + 3, 0⟩ [fm]⊢* ⟨k + 1, 0, 1, 5 * k + 2⟩ := by
  rw [show 2 * k + 3 = 1 + 2 * k + 2 from by ring]
  step fm; step fm
  have h := climb_round k 0 1 2
  simp only [Nat.zero_add] at h
  rw [show 1 + k = k + 1 from by ring, show 2 + 5 * k = 5 * k + 2 from by ring] at h
  exact h

-- R3 chain: a_to_b
theorem a_to_b : ∀ k, ∀ a b d, ⟨a + k, b, 0, d⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a (b + 2) (d + 1))
  ring_nf; finish

-- Even peak resolve
theorem even_peak (k d : ℕ) : ⟨k + 1, 0, 0, d⟩ [fm]⊢* ⟨0, 2 * (k + 1), 0, d + k + 1⟩ := by
  have h := a_to_b (k + 1) 0 0 d
  simp only [Nat.zero_add] at h; exact h

-- Odd peak resolve
theorem odd_peak (k d : ℕ) : ⟨k + 1, 0, 1, d⟩ [fm]⊢* ⟨0, 2 * k + 3, 0, d + k + 4⟩ := by
  step fm; step fm
  have h := a_to_b (k + 1) 0 1 (d + 3)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

-- b_drain by 3
theorem b_drain : ∀ k, ∀ b d, ⟨0, b + 3 * k, 0, d + k⟩ [fm]⊢* ⟨0, b, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  exact ih b d

-- Close remainder 1
theorem close_r1 (d : ℕ) : ⟨0, 1, 0, d + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 4⟩ := by
  execute fm 8

-- Close remainder 2
theorem close_r2 (d : ℕ) : ⟨0, 2, 0, d + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 2⟩ := by
  execute fm 5

-- Transition for d = 6m+2
theorem trans_r2 (m : ℕ) : ⟨0, 0, 0, 6 * m + 2⟩ [fm]⊢* ⟨0, 0, 0, 16 * m + 4⟩ := by
  have h1 := d_to_c (6 * m + 2) 0 0
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 6 * m + 2 = 2 * (3 * m + 1) from by ring]
  apply stepStar_trans (climb_even (3 * m))
  apply stepStar_trans (even_peak (3 * m) (5 * (3 * m) + 2))
  have hb := b_drain (2 * m) 2 (16 * m + 3)
  rw [show 2 + 3 * (2 * m) = 6 * m + 2 from by ring,
      show 16 * m + 3 + 2 * m = 18 * m + 3 from by ring] at hb
  rw [show 2 * (3 * m + 1) = 6 * m + 2 from by ring,
      show 5 * (3 * m) + 2 + 3 * m + 1 = 18 * m + 3 from by ring]
  apply stepStar_trans hb
  exact close_r2 (16 * m + 2)

-- Transition for d = 6m+4
theorem trans_r4 (m : ℕ) : ⟨0, 0, 0, 6 * m + 4⟩ [fm]⊢* ⟨0, 0, 0, 16 * m + 11⟩ := by
  have h1 := d_to_c (6 * m + 4) 0 0
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 6 * m + 4 = 2 * (3 * m + 2) from by ring]
  apply stepStar_trans (climb_even (3 * m + 1))
  apply stepStar_trans (even_peak (3 * m + 1) (5 * (3 * m + 1) + 2))
  have hb := b_drain (2 * m + 1) 1 (16 * m + 8)
  rw [show 1 + 3 * (2 * m + 1) = 6 * m + 4 from by ring,
      show 16 * m + 8 + (2 * m + 1) = 18 * m + 9 from by ring] at hb
  rw [show 2 * (3 * m + 1 + 1) = 6 * m + 4 from by ring,
      show 5 * (3 * m + 1) + 2 + (3 * m + 1) + 1 = 18 * m + 9 from by ring]
  apply stepStar_trans hb
  exact close_r1 (16 * m + 7)

-- Transition for d = 6(m+1)
theorem trans_r0 (m : ℕ) : ⟨0, 0, 0, 6 * (m + 1)⟩ [fm]⊢* ⟨0, 0, 0, 16 * m + 13⟩ := by
  have h1 := d_to_c (6 * (m + 1)) 0 0
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 6 * (m + 1) = 2 * (3 * m + 3) from by ring]
  apply stepStar_trans (climb_even (3 * m + 2))
  apply stepStar_trans (even_peak (3 * m + 2) (5 * (3 * m + 2) + 2))
  have hb := b_drain (2 * m + 2) 0 (16 * m + 13)
  rw [show 0 + 3 * (2 * m + 2) = 6 * m + 6 from by ring,
      show 16 * m + 13 + (2 * m + 2) = 18 * m + 15 from by ring] at hb
  rw [show 2 * (3 * m + 2 + 1) = 6 * m + 6 from by ring,
      show 5 * (3 * m + 2) + 2 + (3 * m + 2) + 1 = 18 * m + 15 from by ring]
  exact hb

-- Transition for d = 6m+3
theorem trans_r3 (m : ℕ) : ⟨0, 0, 0, 6 * m + 3⟩ [fm]⊢* ⟨0, 0, 0, 16 * m + 5⟩ := by
  have h1 := d_to_c (6 * m + 3) 0 0
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 6 * m + 3 = 2 * (3 * m) + 3 from by ring]
  apply stepStar_trans (climb_odd (3 * m))
  apply stepStar_trans (odd_peak (3 * m) (5 * (3 * m) + 2))
  have hb := b_drain (2 * m + 1) 0 (16 * m + 5)
  rw [show 0 + 3 * (2 * m + 1) = 6 * m + 3 from by ring,
      show 16 * m + 5 + (2 * m + 1) = 18 * m + 6 from by ring] at hb
  rw [show 2 * (3 * m) + 3 = 6 * m + 3 from by ring,
      show 5 * (3 * m) + 2 + 3 * m + 4 = 18 * m + 6 from by ring]
  exact hb

-- Transition for d = 6m+5
theorem trans_r5 (m : ℕ) : ⟨0, 0, 0, 6 * m + 5⟩ [fm]⊢* ⟨0, 0, 0, 16 * m + 12⟩ := by
  have h1 := d_to_c (6 * m + 5) 0 0
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 6 * m + 5 = 2 * (3 * m + 1) + 3 from by ring]
  apply stepStar_trans (climb_odd (3 * m + 1))
  apply stepStar_trans (odd_peak (3 * m + 1) (5 * (3 * m + 1) + 2))
  have hb := b_drain (2 * m + 1) 2 (16 * m + 11)
  rw [show 2 + 3 * (2 * m + 1) = 6 * m + 5 from by ring,
      show 16 * m + 11 + (2 * m + 1) = 18 * m + 12 from by ring] at hb
  rw [show 2 * (3 * m + 1) + 3 = 6 * m + 5 from by ring,
      show 5 * (3 * m + 1) + 2 + (3 * m + 1) + 4 = 18 * m + 12 from by ring]
  apply stepStar_trans hb
  exact close_r2 (16 * m + 10)

-- Transition for d = 6m+7
theorem trans_r1 (m : ℕ) : ⟨0, 0, 0, 6 * m + 7⟩ [fm]⊢* ⟨0, 0, 0, 16 * m + 19⟩ := by
  have h1 := d_to_c (6 * m + 7) 0 0
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 6 * m + 7 = 2 * (3 * m + 2) + 3 from by ring]
  apply stepStar_trans (climb_odd (3 * m + 2))
  apply stepStar_trans (odd_peak (3 * m + 2) (5 * (3 * m + 2) + 2))
  have hb := b_drain (2 * m + 2) 1 (16 * m + 16)
  rw [show 1 + 3 * (2 * m + 2) = 6 * m + 7 from by ring,
      show 16 * m + 16 + (2 * m + 2) = 18 * m + 18 from by ring] at hb
  rw [show 2 * (3 * m + 2) + 3 = 6 * m + 7 from by ring,
      show 5 * (3 * m + 2) + 2 + (3 * m + 2) + 4 = 18 * m + 18 from by ring]
  apply stepStar_trans hb
  exact close_r1 (16 * m + 15)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d, q = ⟨0, 0, 0, d⟩ ∧ d ≥ 2)
  · intro c ⟨d, hq, hd⟩; subst hq
    have h6 : d % 6 < 6 := Nat.mod_lt _ (by omega)
    have ⟨m, hm⟩ : ∃ m, d = 6 * m + d % 6 := ⟨d / 6, by omega⟩
    rcases h6a : d % 6 with _ | _ | _ | _ | _ | _
    · -- d ≡ 0 mod 6
      have hm1 : m ≥ 1 := by omega
      obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm1
      have hd_eq : d = 6 * (m' + 1) := by omega
      rw [hd_eq]
      exact ⟨⟨0, 0, 0, 16 * m' + 13⟩, ⟨16 * m' + 13, rfl, by omega⟩,
        stepStar_stepPlus (trans_r0 m') (by simp [Q]; omega)⟩
    · -- d ≡ 1 mod 6
      have hm1 : m ≥ 1 := by omega
      obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm1
      have hd_eq : d = 6 * m' + 7 := by omega
      rw [hd_eq]
      exact ⟨⟨0, 0, 0, 16 * m' + 19⟩, ⟨16 * m' + 19, rfl, by omega⟩,
        stepStar_stepPlus (trans_r1 m') (by simp [Q]; omega)⟩
    · -- d ≡ 2 mod 6
      have hd_eq : d = 6 * m + 2 := by omega
      rw [hd_eq]
      exact ⟨⟨0, 0, 0, 16 * m + 4⟩, ⟨16 * m + 4, rfl, by omega⟩,
        stepStar_stepPlus (trans_r2 m) (by simp [Q]; omega)⟩
    · -- d ≡ 3 mod 6
      have hd_eq : d = 6 * m + 3 := by omega
      rw [hd_eq]
      exact ⟨⟨0, 0, 0, 16 * m + 5⟩, ⟨16 * m + 5, rfl, by omega⟩,
        stepStar_stepPlus (trans_r3 m) (by simp [Q]; omega)⟩
    · -- d ≡ 4 mod 6
      have hd_eq : d = 6 * m + 4 := by omega
      rw [hd_eq]
      exact ⟨⟨0, 0, 0, 16 * m + 11⟩, ⟨16 * m + 11, rfl, by omega⟩,
        stepStar_stepPlus (trans_r4 m) (by simp [Q]; omega)⟩
    · -- d ≡ 5 mod 6
      have hd_eq : d = 6 * m + 5 := by omega
      rw [hd_eq]
      exact ⟨⟨0, 0, 0, 16 * m + 12⟩, ⟨16 * m + 12, rfl, by omega⟩,
        stepStar_stepPlus (trans_r5 m) (by simp [Q]; omega)⟩
  · exact ⟨2, rfl, le_refl 2⟩

end Sz22_2003_unofficial_22
