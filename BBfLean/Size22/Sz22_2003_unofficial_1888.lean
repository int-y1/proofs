import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1888: [9/35, 5/33, 98/3, 11/7, 175/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  2  0
 0  0  0 -1  1
-1  0  2  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1888

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

-- R4 repeated: move d to e (general, with initial e)
theorem d_to_e : ∀ k d, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show d + (k + 1) = d + 1 + k from by ring]
    apply stepStar_trans (ih (d + 1))
    rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm; finish

-- R4 full: move all d to e
theorem d_to_e_full : ⟨a, 0, 0, d, 0⟩ [fm]⊢* ⟨a, 0, 0, 0, d⟩ := by
  rw [show d = 0 + d from by ring]
  exact d_to_e d 0

-- R4 step plus: at least one step when d >= 1
theorem d_to_e_plus : ⟨a, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a, 0, 0, 0, d + 1⟩ := by
  step fm
  rw [show d = 0 + d from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (d_to_e d 0)
  ring_nf; finish

-- R3 repeated: drain b
theorem r3_chain : ∀ k a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) (d + 2))
    ring_nf; finish

-- R5+R1+R2+R2 repeated: drain a and e
theorem drain : ∀ k a c, ⟨a + k, 0, c, 0, 2 * k + r⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, r⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · ring_nf; exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring,
        show 2 * (k + 1) + r = 2 * k + r + 1 + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a (c + 3))
    ring_nf; finish

theorem endgame_odd : ⟨a + 1, 0, c, 0, 1⟩ [fm]⊢* ⟨a + 1, 0, c + 2, 2, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem endgame_even : ⟨a + 1, 0, c, 0, 0⟩ [fm]⊢* ⟨a, 0, c + 2, 1, 0⟩ := by
  step fm; finish

theorem r1r3_start : ⟨a, 0, c + 1, 1, 0⟩ [fm]⊢* ⟨a + 1, 1, c, 2, 0⟩ := by
  step fm; step fm; finish

theorem r1r1r3_chain : ∀ k a b, ⟨a, b, c + 2 * k, 2, 0⟩ [fm]⊢* ⟨a + k, b + 3 * k, c, 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · ring_nf; exists 0
  · rw [show c + 2 * (k + 1) = c + 2 * k + 1 + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    have h1 : (⟨a, b, c + 2 * k + 1 + 1, 1 + 1, 0⟩ : Q) [fm]⊢ ⟨a, b + 2, c + 2 * k + 1, 1, 0⟩ := by
      simp [fm]
    apply stepStar_trans (step_stepStar h1)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    have h2 : (⟨a, b + 2, c + 2 * k + 1, 0 + 1, 0⟩ : Q) [fm]⊢ ⟨a, b + 4, c + 2 * k, 0, 0⟩ := by
      simp [fm]
    apply stepStar_trans (step_stepStar h2)
    have h3 : (⟨a, (b + 3) + 1, c + 2 * k, 0, 0⟩ : Q) [fm]⊢ ⟨a + 1, b + 3, c + 2 * k, 2, 0⟩ := by
      simp [fm]
    rw [show b + 4 = (b + 3) + 1 from by ring]
    apply stepStar_trans (step_stepStar h3)
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 3))
    ring_nf; finish

theorem r1_terminal : ⟨a, b, 1, 2, 0⟩ [fm]⊢* ⟨a, b + 2, 0, 1, 0⟩ := by
  step fm; finish

-- Odd d = 4j+1 (K=2j)
theorem odd_even_k :
    ⟨m + 2 * j + 1, 0, 0, 4 * j + 1, 0⟩ [fm]⊢⁺ ⟨m + 12 * j + 5, 0, 0, 18 * j + 8, 0⟩ := by
  rw [show 4 * j + 1 = (4 * j) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (d_to_e_plus (a := m + 2 * j + 1) (d := 4 * j))
  rw [show (4 * j + 1 : ℕ) = 2 * (2 * j) + 1 from by ring,
      show m + 2 * j + 1 = (m + 1) + 2 * j from by ring]
  apply stepStar_trans (drain (r := 1) (2 * j) (m + 1) 0)
  rw [show 0 + 3 * (2 * j) = 6 * j from by ring]
  apply stepStar_trans (endgame_odd (a := m) (c := 6 * j))
  rw [show 6 * j + 2 = 0 + 2 * (3 * j + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (c := 0) (3 * j + 1) (m + 1) 0)
  rw [show m + 1 + (3 * j + 1) = m + 3 * j + 2 from by ring,
      show 0 + 3 * (3 * j + 1) = 9 * j + 3 from by ring]
  apply stepStar_trans (r3_chain (9 * j + 3) (m + 3 * j + 2) 2)
  ring_nf; finish

-- Odd d = 4j+3 (K=2j+1)
theorem odd_odd_k :
    ⟨m + 2 * j + 2, 0, 0, 4 * j + 3, 0⟩ [fm]⊢⁺ ⟨m + 12 * j + 11, 0, 0, 18 * j + 17, 0⟩ := by
  rw [show 4 * j + 3 = (4 * j + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (d_to_e_plus (a := m + 2 * j + 2) (d := 4 * j + 2))
  rw [show (4 * j + 2 + 1 : ℕ) = 2 * (2 * j + 1) + 1 from by ring,
      show m + 2 * j + 2 = (m + 1) + (2 * j + 1) from by ring]
  apply stepStar_trans (drain (r := 1) (2 * j + 1) (m + 1) 0)
  rw [show 0 + 3 * (2 * j + 1) = 6 * j + 3 from by ring]
  apply stepStar_trans (endgame_odd (a := m) (c := 6 * j + 3))
  rw [show 6 * j + 3 + 2 = 1 + 2 * (3 * j + 2) from by ring]
  apply stepStar_trans (r1r1r3_chain (c := 1) (3 * j + 2) (m + 1) 0)
  rw [show m + 1 + (3 * j + 2) = m + 3 * j + 3 from by ring,
      show 0 + 3 * (3 * j + 2) = 9 * j + 6 from by ring]
  apply stepStar_trans (r1_terminal (a := m + 3 * j + 3) (b := 9 * j + 6))
  rw [show 9 * j + 6 + 2 = 9 * j + 8 from by ring]
  apply stepStar_trans (r3_chain (9 * j + 8) (m + 3 * j + 3) 1)
  ring_nf; finish

-- Even d = 4(j+1) (K=2(j+1), j >= 0)
theorem even_even_k :
    ⟨m + 2 * (j + 1) + 1, 0, 0, 4 * (j + 1), 0⟩ [fm]⊢⁺
    ⟨m + 12 * (j + 1) + 4, 0, 0, 18 * (j + 1) + 7, 0⟩ := by
  rw [show 4 * (j + 1) = (4 * j + 3) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (d_to_e_plus (a := m + 2 * (j + 1) + 1) (d := 4 * j + 3))
  rw [show (4 * j + 3 + 1 : ℕ) = 2 * (2 * j + 2) + 0 from by ring,
      show m + 2 * (j + 1) + 1 = (m + 1) + (2 * j + 2) from by ring]
  apply stepStar_trans (drain (r := 0) (2 * j + 2) (m + 1) 0)
  rw [show 0 + 3 * (2 * j + 2) = 6 * j + 6 from by ring]
  apply stepStar_trans (endgame_even (a := m) (c := 6 * j + 6))
  rw [show 6 * j + 6 + 2 = (6 * j + 7) + 1 from by ring]
  apply stepStar_trans (r1r3_start (a := m) (c := 6 * j + 7))
  rw [show (6 * j + 7 : ℕ) = 1 + 2 * (3 * j + 3) from by ring]
  apply stepStar_trans (r1r1r3_chain (c := 1) (3 * j + 3) (m + 1) 1)
  rw [show m + 1 + (3 * j + 3) = m + 3 * j + 4 from by ring,
      show 1 + 3 * (3 * j + 3) = 9 * j + 10 from by ring]
  apply stepStar_trans (r1_terminal (a := m + 3 * j + 4) (b := 9 * j + 10))
  rw [show 9 * j + 10 + 2 = 9 * j + 12 from by ring]
  apply stepStar_trans (r3_chain (9 * j + 12) (m + 3 * j + 4) 1)
  ring_nf; finish

-- Even d = 4j+2 (K=2j+1)
theorem even_odd_k :
    ⟨m + 2 * j + 2, 0, 0, 4 * j + 2, 0⟩ [fm]⊢⁺ ⟨m + 12 * j + 10, 0, 0, 18 * j + 16, 0⟩ := by
  rw [show 4 * j + 2 = (4 * j + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (d_to_e_plus (a := m + 2 * j + 2) (d := 4 * j + 1))
  rw [show (4 * j + 1 + 1 : ℕ) = 2 * (2 * j + 1) + 0 from by ring,
      show m + 2 * j + 2 = (m + 1) + (2 * j + 1) from by ring]
  apply stepStar_trans (drain (r := 0) (2 * j + 1) (m + 1) 0)
  rw [show 0 + 3 * (2 * j + 1) = 6 * j + 3 from by ring]
  apply stepStar_trans (endgame_even (a := m) (c := 6 * j + 3))
  rw [show 6 * j + 3 + 2 = (6 * j + 4) + 1 from by ring]
  apply stepStar_trans (r1r3_start (a := m) (c := 6 * j + 4))
  rw [show (6 * j + 4 : ℕ) = 0 + 2 * (3 * j + 2) from by ring]
  apply stepStar_trans (r1r1r3_chain (c := 0) (3 * j + 2) (m + 1) 1)
  rw [show m + 1 + (3 * j + 2) = m + 3 * j + 3 from by ring,
      show 1 + 3 * (3 * j + 2) = 9 * j + 7 from by ring]
  apply stepStar_trans (r3_chain (9 * j + 7) (m + 3 * j + 3) 2)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 7, 0⟩)
  · execute fm 7
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ 2 * a ≥ d + 1)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    obtain ⟨j, rfl | rfl | rfl | rfl⟩ : ∃ j, d = 4 * j ∨ d = 4 * j + 1 ∨ d = 4 * j + 2 ∨ d = 4 * j + 3 :=
      ⟨d / 4, by omega⟩
    · -- d = 4j, j >= 1
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 * (j + 1) + 1 := ⟨a - (2 * j + 3), by omega⟩
      exact ⟨_, ⟨m + 12 * (j + 1) + 4, 18 * (j + 1) + 7, rfl, by omega, by omega⟩,
        even_even_k⟩
    · -- d = 4j+1
      obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 * j + 1 := ⟨a - (2 * j + 1), by omega⟩
      exact ⟨_, ⟨m + 12 * j + 5, 18 * j + 8, rfl, by omega, by omega⟩,
        odd_even_k⟩
    · -- d = 4j+2
      obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 * j + 2 := ⟨a - (2 * j + 2), by omega⟩
      exact ⟨_, ⟨m + 12 * j + 10, 18 * j + 16, rfl, by omega, by omega⟩,
        even_odd_k⟩
    · -- d = 4j+3
      obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 * j + 2 := ⟨a - (2 * j + 2), by omega⟩
      exact ⟨_, ⟨m + 12 * j + 11, 18 * j + 17, rfl, by omega, by omega⟩,
        odd_odd_k⟩
  · exact ⟨4, 7, rfl, by omega, by omega⟩
