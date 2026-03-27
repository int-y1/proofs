import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #226: [108/35, 5/22, 49/2, 11/3, 5/7]

Vector representation:
```
 2  3 -1 -1  0
-1  0  1  0 -1
-1  0  0  2  0
 0 -1  0  0  1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_226

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+3, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: transfer b to e
theorem b_to_e : ∀ k b d e,
    ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · simp; exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 1))
    rw [show e + 1 + k = e + (k + 1) from by ring]
    finish

-- Inner loop: j (R2, R1) pairs
theorem inner_loop : ∀ j d e,
    ⟨2, 3, 0, j + d, j + e⟩ [fm]⊢* ⟨j + 2, 3 * j + 3, 0, d, e⟩ := by
  intro j; induction' j with j ih <;> intro d e
  · simp; exists 0
  · rw [show j + 1 + d = j + (d + 1) from by ring,
        show j + 1 + e = j + (e + 1) from by ring]
    apply stepStar_trans (ih (d + 1) (e + 1))
    step fm; step fm
    ring_nf; finish

-- R2 chain: transfer e to c (when d=0)
theorem e_to_c : ∀ k a b c,
    ⟨a + k, b, c, 0, k⟩ [fm]⊢* ⟨a, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · simp; exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (c + 1))
    rw [show c + 1 + k = c + (k + 1) from by ring]
    finish

-- R3+R1+R1: drain 2 from c
theorem c_drain_pair (a b c : ℕ) :
    ⟨a + 1, b, c + 2, 0, 0⟩ [fm]⊢* ⟨a + 4, b + 6, c, 0, 0⟩ := by
  step fm; step fm; step fm
  ring_nf; finish

-- Iterated c drain (even)
theorem c_drain_even : ∀ k a b,
    ⟨a + 1, b, 2 * k, 0, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, b + 6 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · simp; exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans (c_drain_pair a b (2 * k))
    rw [show a + 4 = a + 3 + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (b + 6))
    rw [show a + 3 + 3 * k + 1 = a + 3 * (k + 1) + 1 from by ring,
        show b + 6 + 6 * k = b + 6 * (k + 1) from by ring]
    finish

-- Iterated c drain (odd): drain 2k, leaving 1
theorem c_drain_odd : ∀ k a b,
    ⟨a + 1, b, 2 * k + 1, 0, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, b + 6 * k, 1, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · simp; exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    apply stepStar_trans (c_drain_pair a b (2 * k + 1))
    rw [show a + 4 = a + 3 + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (b + 6))
    rw [show a + 3 + 3 * k + 1 = a + 3 * (k + 1) + 1 from by ring,
        show b + 6 + 6 * k = b + 6 * (k + 1) from by ring]
    finish

-- R3 chain: transfer a to d
theorem a_to_d : ∀ k a b d,
    ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · simp; exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (d + 2))
    rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]
    finish

-- Odd tail: (a+2, b, 1, 0, 0) → R3,R1,R3 → (a+2, b+3, 0, 3, 0)
theorem odd_tail (a b : ℕ) :
    ⟨a + 2, b, 1, 0, 0⟩ [fm]⊢* ⟨a + 2, b + 3, 0, 3, 0⟩ := by
  step fm; step fm; step fm
  ring_nf; finish

-- Main transition for EVEN case: b = d + 2*m
theorem main_even (d m : ℕ) (_hd : d ≥ 1) (hle : d + 2 * m ≤ 2 * d + 1) :
    ⟨0, d + 2 * m, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨0, 3 * d + 6 * m + 3, 0, 2 * d + 2 * m + 4, 0⟩ := by
  have h1 := b_to_e (d + 2 * m) 0 (d + 2) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  step fm; step fm
  apply stepStar_trans
  · exact inner_loop d 0 (2 * m)
  apply stepStar_trans
  · have h4 := e_to_c (2 * m) (d + 2 - 2 * m) (3 * d + 3) 0
    rw [show d + 2 - 2 * m + 2 * m = d + 2 from by omega,
        show (0 : ℕ) + 2 * m = 2 * m from by ring] at h4
    exact h4
  apply stepStar_trans
  · have h5 := c_drain_even m (d + 2 - 2 * m - 1) (3 * d + 3)
    rw [show d + 2 - 2 * m - 1 + 1 = d + 2 - 2 * m from by omega,
        show d + 2 - 2 * m - 1 + 3 * m + 1 = d + m + 2 from by omega] at h5
    exact h5
  have h6 := a_to_d (d + m + 2) 0 (3 * d + 3 + 6 * m) 0
  rw [show (0 : ℕ) + (d + m + 2) = d + m + 2 from by ring,
      show (0 : ℕ) + 2 * (d + m + 2) = 2 * d + 2 * m + 4 from by ring] at h6
  apply stepStar_trans h6
  rw [show 3 * d + 3 + 6 * m = 3 * d + 6 * m + 3 from by ring]
  finish

-- Main transition for ODD case: b = d + 2*m + 1
theorem main_odd (d m : ℕ) (hd : d ≥ 1) (hle : d + 2 * m + 1 ≤ 2 * d + 1) :
    ⟨0, d + 2 * m + 1, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨0, 3 * d + 6 * m + 6, 0, 2 * d + 2 * m + 5, 0⟩ := by
  have h1 := b_to_e (d + 2 * m + 1) 0 (d + 2) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  step fm; step fm
  apply stepStar_trans
  · exact inner_loop d 0 (2 * m + 1)
  apply stepStar_trans
  · have h4 := e_to_c (2 * m + 1) (d + 2 - (2 * m + 1)) (3 * d + 3) 0
    rw [show d + 2 - (2 * m + 1) + (2 * m + 1) = d + 2 from by omega,
        show (0 : ℕ) + (2 * m + 1) = 2 * m + 1 from by ring] at h4
    exact h4
  apply stepStar_trans
  · have h5 := c_drain_odd m (d + 2 - (2 * m + 1) - 1) (3 * d + 3)
    rw [show d + 2 - (2 * m + 1) - 1 + 1 = d + 2 - (2 * m + 1) from by omega,
        show d + 2 - (2 * m + 1) - 1 + 3 * m + 1 = d + m + 1 from by omega] at h5
    exact h5
  apply stepStar_trans
  · have h6 := odd_tail (d + m + 1 - 2) (3 * d + 3 + 6 * m)
    rw [show d + m + 1 - 2 + 2 = d + m + 1 from by omega] at h6
    exact h6
  have h7 := a_to_d (d + m + 1) 0 (3 * d + 3 + 6 * m + 3) 3
  rw [show (0 : ℕ) + (d + m + 1) = d + m + 1 from by ring,
      show 3 + 2 * (d + m + 1) = 2 * d + 2 * m + 5 from by ring] at h7
  apply stepStar_trans h7
  rw [show 3 * d + 3 + 6 * m + 3 = 3 * d + 6 * m + 6 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 3, 0, 4, 0⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b d, q = ⟨0, b, 0, d + 2, 0⟩ ∧ d ≥ 1 ∧ d ≤ b ∧ b ≤ 2 * d + 1)
  · intro c ⟨b, d, hq, hd, hdb, hbd⟩; subst hq
    rcases Nat.even_or_odd (b - d) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hb : b = d + 2 * m := by omega
      subst hb
      exact ⟨⟨0, 3 * d + 6 * m + 3, 0, 2 * d + 2 * m + 4, 0⟩,
        ⟨3 * d + 6 * m + 3, 2 * d + 2 * m + 2,
         by ring_nf, by omega, by omega, by omega⟩,
        main_even d m hd hbd⟩
    · have hb : b = d + 2 * m + 1 := by omega
      subst hb
      exact ⟨⟨0, 3 * d + 6 * m + 6, 0, 2 * d + 2 * m + 5, 0⟩,
        ⟨3 * d + 6 * m + 6, 2 * d + 2 * m + 3,
         by ring_nf, by omega, by omega, by omega⟩,
        main_odd d m hd hbd⟩
  · exact ⟨3, 2, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_226
