import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #19: [1/135, 7/15, 18/7, 125/2, 3/5]

Vector representation:
```
 0 -3 -1  0
 0 -1 -1  1
 1  2  0 -1
-1  0  3  0
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_19

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+3, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4 drain: (n+1, 0, C, 0) ⊢* (0, 0, C+3*(n+1), 0)
theorem a_drain : ∀ n, ∀ C, (⟨n + 1, 0, C, 0⟩ : Q) [fm]⊢* ⟨0, 0, C + 3 * (n + 1), 0⟩ := by
  intro n; induction' n with n ih <;> intro C
  · step fm; ring_nf; finish
  rw [show C + 3 * ((n + 1) + 1) = (C + 3) + 3 * (n + 1) from by ring]
  step fm; exact ih (C + 3)

-- R3 chain (c=0): (A, B, 0, k+1) ⊢* (A+k+1, B+2*(k+1), 0, 0)
theorem r3_chain : ∀ k, ∀ A B,
    (⟨A, B, 0, k + 1⟩ : Q) [fm]⊢* ⟨A + k + 1, B + 2 * (k + 1), 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B
  · step fm; ring_nf; finish
  rw [show A + (k + 1) + 1 = (A + 1) + k + 1 from by ring,
      show B + 2 * ((k + 1) + 1) = (B + 2) + 2 * (k + 1) from by ring]
  step fm; exact ih (A + 1) (B + 2)

-- Climb rounds of R2, R2, R3
theorem climb_rounds : ∀ m, ∀ k C D,
    (⟨k, 2, C + 2 * (m + 1), D⟩ : Q) [fm]⊢* ⟨k + m + 1, 2, C, D + m + 1⟩ := by
  intro m; induction' m with m ih <;> intro k C D
  · step fm; step fm; step fm; ring_nf; finish
  rw [show C + 2 * ((m + 1) + 1) = (C + 2 * (m + 1)) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (k + 1) C (D + 1)); ring_nf; finish

-- Full climb (even c): (0, 0, 2*m+2, 0) ⊢* (2*m+1, 2*m+2, 0, 0)
theorem climb_even (m : ℕ) :
    (⟨0, 0, 2 * m + 2, 0⟩ : Q) [fm]⊢* ⟨2 * m + 1, 2 * m + 2, 0, 0⟩ := by
  rw [show 2 * m + 2 = 0 + 2 * (m + 1) from by ring]
  step fm; step fm; step fm
  rcases m with _ | m
  · exists 0
  · apply stepStar_trans (climb_rounds m 1 0 0)
    rw [show 1 + m + 1 = m + 2 from by ring, show 0 + m + 1 = m + 1 from by ring]
    apply stepStar_trans (r3_chain m (m + 2) 2)
    ring_nf; finish

-- Full climb (odd c): (0, 0, 2*m+3, 0) ⊢* (2*m+2, 2*m+3, 0, 0)
theorem climb_odd (m : ℕ) :
    (⟨0, 0, 2 * m + 3, 0⟩ : Q) [fm]⊢* ⟨2 * m + 2, 2 * m + 3, 0, 0⟩ := by
  rw [show 2 * m + 3 = 1 + 2 * (m + 1) from by ring]
  step fm; step fm; step fm
  rcases m with _ | m
  · step fm; step fm; finish
  · apply stepStar_trans (climb_rounds m 1 1 0)
    rw [show 1 + m + 1 = m + 2 from by ring, show 0 + m + 1 = m + 1 from by ring]
    step fm
    rw [show m + 1 + 1 = (m + 1) + 1 from by ring]
    apply stepStar_trans (r3_chain (m + 1) (m + 2) 1)
    ring_nf; finish

-- Big round: (A+1, B+9, 0, 0) ⊢* (A, B, 0, 0)
theorem big_round (A B : ℕ) :
    (⟨A + 1, B + 9, 0, 0⟩ : Q) [fm]⊢* ⟨A, B, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Iterated big rounds
theorem big_rounds : ∀ k, ∀ A B,
    (⟨A + k + 1, B + 9 * (k + 1), 0, 0⟩ : Q) [fm]⊢* ⟨A, B, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B
  · rw [show A + 0 + 1 = A + 1 from by ring, show B + 9 * 1 = B + 9 from by ring]
    exact big_round A B
  rw [show A + (k + 1) + 1 = (A + k + 1) + 1 from by ring,
      show B + 9 * ((k + 1) + 1) = (B + 9 * (k + 1)) + 9 from by ring]
  apply stepStar_trans (big_round _ _); exact ih A B

-- Tail B=8: (a+1, 8, 0, 0) ⊢* (a+1, 3, 0, 0)
theorem tail_8 (a : ℕ) : (⟨a + 1, 8, 0, 0⟩ : Q) [fm]⊢* ⟨a + 1, 3, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Tail B=5: (a+1, 5, 0, 0) ⊢* (a+3, 3, 0, 0)
theorem tail_5 (a : ℕ) : (⟨a + 1, 5, 0, 0⟩ : Q) [fm]⊢* ⟨a + 3, 3, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Tail B=2: (a+1, 2, 0, 0) ⊢* (a+5, 3, 0, 0)
theorem tail_2 (a : ℕ) : (⟨a + 1, 2, 0, 0⟩ : Q) [fm]⊢* ⟨a + 5, 3, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Climb helper: handles both parities
theorem climb (c : ℕ) : (⟨0, 0, c + 3, 0⟩ : Q) [fm]⊢* ⟨c + 2, c + 3, 0, 0⟩ := by
  rcases Nat.even_or_odd c with ⟨i, hi⟩ | ⟨i, hi⟩
  · -- c = 2i, c+3 = 2i+3
    rw [show c + 3 = 2 * i + 3 from by omega,
        show c + 2 = 2 * i + 2 from by omega]
    exact climb_odd i
  · -- c = 2i+1, c+3 = 2i+4 = 2*(i+1)+2
    rw [show c + 3 = 2 * (i + 1) + 2 from by omega,
        show c + 2 = 2 * (i + 1) + 1 from by omega]
    exact climb_even (i + 1)

-- Main transition: n mod 3 = 0 (n = 3j)
theorem main_mod0 (j : ℕ) : (⟨3 * j + 2, 3, 0, 0⟩ : Q) [fm]⊢⁺ ⟨8 * j + 6, 3, 0, 0⟩ := by
  rw [show 3 * j + 2 = (3 * j + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨3 * j + 1, 3, 3, 0⟩)
  · simp [fm]
  step fm
  rw [show 3 * j + 1 = (3 * j) + 1 from by ring]
  apply stepStar_trans (a_drain (3 * j) 2)
  rw [show 2 + 3 * (3 * j + 1) = 9 * j + 5 from by ring]
  apply stepStar_trans (c₂ := ⟨9 * j + 4, 9 * j + 5, 0, 0⟩)
  · rw [show 9 * j + 5 = (9 * j + 2) + 3 from by ring,
        show 9 * j + 4 = (9 * j + 2) + 2 from by ring]
    exact climb (9 * j + 2)
  apply stepStar_trans (c₂ := ⟨8 * j + 4, 5, 0, 0⟩)
  · rcases j with _ | j
    · simp; exists 0
    · rw [show 9 * (j + 1) + 4 = (8 * (j + 1) + 4) + j + 1 from by ring,
          show 9 * (j + 1) + 5 = 5 + 9 * (j + 1) from by ring]
      exact big_rounds j (8 * (j + 1) + 4) 5
  rw [show 8 * j + 4 = (8 * j + 3) + 1 from by ring,
      show 8 * j + 6 = (8 * j + 3) + 3 from by ring]
  exact tail_5 (8 * j + 3)

-- Main transition: n mod 3 = 1 (n = 3j+1)
theorem main_mod1 (j : ℕ) : (⟨3 * j + 3, 3, 0, 0⟩ : Q) [fm]⊢⁺ ⟨8 * j + 7, 3, 0, 0⟩ := by
  rw [show 3 * j + 3 = (3 * j + 2) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨3 * j + 2, 3, 3, 0⟩)
  · simp [fm]
  step fm
  rw [show 3 * j + 2 = (3 * j + 1) + 1 from by ring]
  apply stepStar_trans (a_drain (3 * j + 1) 2)
  rw [show 2 + 3 * ((3 * j + 1) + 1) = 9 * j + 8 from by ring]
  apply stepStar_trans (c₂ := ⟨9 * j + 7, 9 * j + 8, 0, 0⟩)
  · rw [show 9 * j + 8 = (9 * j + 5) + 3 from by ring,
        show 9 * j + 7 = (9 * j + 5) + 2 from by ring]
    exact climb (9 * j + 5)
  apply stepStar_trans (c₂ := ⟨8 * j + 7, 8, 0, 0⟩)
  · rcases j with _ | j
    · simp; exists 0
    · rw [show 9 * (j + 1) + 7 = (8 * (j + 1) + 7) + j + 1 from by ring,
          show 9 * (j + 1) + 8 = 8 + 9 * (j + 1) from by ring]
      exact big_rounds j (8 * (j + 1) + 7) 8
  rw [show 8 * j + 7 = (8 * j + 6) + 1 from by ring]
  exact tail_8 (8 * j + 6)

-- Main transition: n mod 3 = 2 (n = 3j+2)
theorem main_mod2 (j : ℕ) : (⟨3 * j + 4, 3, 0, 0⟩ : Q) [fm]⊢⁺ ⟨8 * j + 13, 3, 0, 0⟩ := by
  rw [show 3 * j + 4 = (3 * j + 3) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨3 * j + 3, 3, 3, 0⟩)
  · simp [fm]
  step fm
  rw [show 3 * j + 3 = (3 * j + 2) + 1 from by ring]
  apply stepStar_trans (a_drain (3 * j + 2) 2)
  rw [show 2 + 3 * ((3 * j + 2) + 1) = 9 * j + 11 from by ring]
  apply stepStar_trans (c₂ := ⟨9 * j + 10, 9 * j + 11, 0, 0⟩)
  · rw [show 9 * j + 11 = (9 * j + 8) + 3 from by ring,
        show 9 * j + 10 = (9 * j + 8) + 2 from by ring]
    exact climb (9 * j + 8)
  apply stepStar_trans (c₂ := ⟨8 * j + 9, 2, 0, 0⟩)
  · rw [show 9 * j + 10 = (8 * j + 9) + j + 1 from by ring,
        show 9 * j + 11 = 2 + 9 * (j + 1) from by ring]
    exact big_rounds j (8 * j + 9) 2
  rw [show 8 * j + 9 = (8 * j + 8) + 1 from by ring,
      show 8 * j + 13 = (8 * j + 8) + 5 from by ring]
  exact tail_2 (8 * j + 8)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 3, 0, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨n + 2, 3, 0, 0⟩)
  · intro c ⟨n, hq⟩; subst hq
    have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hmod with h | h | h
    · obtain ⟨j, hj⟩ := Nat.dvd_of_mod_eq_zero h
      rw [show n + 2 = 3 * j + 2 from by omega]
      exact ⟨_, ⟨8 * j + 4, rfl⟩, main_mod0 j⟩
    · have ⟨j, hj⟩ : ∃ j, n = 3 * j + 1 := ⟨n / 3, by omega⟩
      rw [show n + 2 = 3 * j + 3 from by omega]
      exact ⟨_, ⟨8 * j + 5, rfl⟩, main_mod1 j⟩
    · have ⟨j, hj⟩ : ∃ j, n = 3 * j + 2 := ⟨n / 3, by omega⟩
      rw [show n + 2 = 3 * j + 4 from by omega]
      exact ⟨_, ⟨8 * j + 11, rfl⟩, main_mod2 j⟩
  · exact ⟨0, rfl⟩

end Sz22_2003_unofficial_19
