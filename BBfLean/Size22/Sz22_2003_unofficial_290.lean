import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #290: [14/15, 9/22, 25/2, 11/49, 9/5]

Vector representation:
```
 1 -1 -1  1  0
-1  2  0  0 -1
-1  0  2  0  0
 0  0  0 -2  1
 0  2 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_290

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R4 repeated: drain d into e
theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d + 2 * k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
  step fm
  have h := ih c d (e + 1)
  rw [show e + 1 + k = e + (k + 1) from by ring] at h
  exact h

-- R3 repeated: drain a into c (when b=0, e=0)
theorem r3_chain : ∀ k a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  have h := ih a (c + 2) d
  rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring] at h
  exact h

-- R2 repeated: drain a and e into b (when c = 0)
theorem r2_chain : ∀ k a b d, ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show (k : ℕ) + 1 = k + 1 from rfl]
  step fm
  have h := ih a (b + 2) d
  rw [show b + 2 + 2 * k = b + 2 * (k + 1) from by ring] at h
  exact h

-- Middle phase single step: 3 steps R1, R1, R2
theorem middle_step (m c d e : ℕ) :
    ⟨m, 2, c + 2, d, e + 1⟩ [fm]⊢* ⟨m + 1, 2, c, d + 2, e⟩ := by
  rw [show c + 2 = (c + 1) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  show ⟨m + 1, 0 + 1, c + 1, d + 1, e + 1⟩ [fm]⊢* _
  step fm
  show ⟨(m + 1) + 1, 0, c, d + 2, e + 1⟩ [fm]⊢* _
  step fm
  finish

-- Middle phase chain
theorem middle_chain : ∀ k m c d e,
    ⟨m, 2, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨m + k, 2, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro m c d e
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  apply stepStar_trans (middle_step m (c + 2 * k) d (e + k))
  have h := ih (m + 1) c (d + 2) e
  rw [show m + 1 + k = m + (k + 1) from by ring,
      show d + 2 + 2 * k = d + 2 * (k + 1) from by ring] at h
  exact h

-- Rearrange phase single step: R1, R1, R3
theorem rearrange_step (a b d : ℕ) :
    ⟨a, b + 2, 2, d, 0⟩ [fm]⊢* ⟨a + 1, b, 2, d + 2, 0⟩ := by
  rw [show b + 2 = (b + 1) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  show ⟨a + 1, b + 1, 0 + 1, d + 1, 0⟩ [fm]⊢* _
  step fm
  show ⟨(a + 1) + 1, b, 0, d + 2, 0⟩ [fm]⊢* _
  step fm
  finish

-- Rearrange phase chain
theorem rearrange_chain : ∀ k a b d,
    ⟨a, b + 2 * k, 2, d, 0⟩ [fm]⊢* ⟨a + k, b, 2, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
  apply stepStar_trans (rearrange_step a (b + 2 * k) d)
  have h := ih (a + 1) b (d + 2)
  rw [show a + 1 + k = a + (k + 1) from by ring,
      show d + 2 + 2 * k = d + 2 * (k + 1) from by ring] at h
  exact h

-- Even N = 2*(m+1): (1, 2m+2, 0, 2m+2, 0) →⁺ (1, 2m+3, 0, 2m+3, 0)
theorem cycle_even (m : ℕ) :
    ⟨1, 2 * m + 2, 0, 2 * m + 2, 0⟩ [fm]⊢⁺ ⟨1, 2 * m + 3, 0, 2 * m + 3, 0⟩ := by
  -- R3 step
  have h_r3_step : (⟨1, 2 * m + 2, 0, 2 * m + 2, 0⟩ : Q) [fm]⊢ ⟨0, 2 * m + 2, 2, 2 * m + 2, 0⟩ := by
    show fm ⟨0 + 1, 2 * m + 2, 0, 2 * m + 2, 0⟩ = some _; rfl
  apply step_stepStar_stepPlus h_r3_step
  -- rearrange chain
  have h_rearr := rearrange_chain (m + 1) 0 0 (2 * m + 2)
  simp only [Nat.zero_add] at h_rearr
  rw [show 2 * (m + 1) = 2 * m + 2 from by ring] at h_rearr
  rw [show 2 * m + 2 + (2 * m + 2) = 4 * m + 4 from by ring] at h_rearr
  apply stepStar_trans h_rearr
  -- r3 chain
  have h_r3c := r3_chain (m + 1) 0 2 (4 * m + 4)
  simp only [Nat.zero_add] at h_r3c
  rw [show 2 + 2 * (m + 1) = 2 * m + 4 from by ring] at h_r3c
  apply stepStar_trans h_r3c
  -- R4 chain
  have h_r4 := r4_chain (2 * m + 2) (2 * m + 4) 0 0
  simp only [Nat.zero_add] at h_r4
  rw [show 2 * (2 * m + 2) = 4 * m + 4 from by ring] at h_r4
  apply stepStar_trans h_r4
  -- R5 step
  have h_r5 : (⟨0, 0, 2 * m + 4, 0, 2 * m + 2⟩ : Q) [fm]⊢ ⟨0, 2, 2 * m + 3, 0, 2 * m + 2⟩ := by
    show fm ⟨0, 0, (2 * m + 3) + 1, 0, 2 * m + 2⟩ = some _; rfl
  apply stepStar_trans (step_stepStar h_r5)
  -- Middle chain
  have h_mid := middle_chain (m + 1) 0 1 0 (m + 1)
  simp only [Nat.zero_add] at h_mid
  rw [show 1 + 2 * (m + 1) = 2 * m + 3 from by ring,
      show m + 1 + (m + 1) = 2 * m + 2 from by ring,
      show 2 * (m + 1) = 2 * m + 2 from by ring] at h_mid
  apply stepStar_trans h_mid
  -- R1 step
  have h_r1 : (⟨m + 1, 2, 1, 2 * m + 2, m + 1⟩ : Q) [fm]⊢ ⟨m + 2, 1, 0, 2 * m + 3, m + 1⟩ := by rfl
  apply stepStar_trans (step_stepStar h_r1)
  -- R2 chain
  have h_r2 := r2_chain (m + 1) 1 1 (2 * m + 3)
  rw [show 1 + (m + 1) = m + 2 from by ring,
      show 1 + 2 * (m + 1) = 2 * m + 3 from by ring] at h_r2
  exact h_r2

-- Odd N = 2*m+3: (1, 2m+3, 0, 2m+3, 0) →⁺ (1, 2m+4, 0, 2m+4, 0)
theorem cycle_odd (m : ℕ) :
    ⟨1, 2 * m + 3, 0, 2 * m + 3, 0⟩ [fm]⊢⁺ ⟨1, 2 * m + 4, 0, 2 * m + 4, 0⟩ := by
  -- R3 step
  have h_r3_step : (⟨1, 2 * m + 3, 0, 2 * m + 3, 0⟩ : Q) [fm]⊢ ⟨0, 2 * m + 3, 2, 2 * m + 3, 0⟩ := by
    show fm ⟨0 + 1, 2 * m + 3, 0, 2 * m + 3, 0⟩ = some _; rfl
  apply step_stepStar_stepPlus h_r3_step
  -- rearrange chain
  have h_rearr := rearrange_chain (m + 1) 0 1 (2 * m + 3)
  simp only [Nat.zero_add] at h_rearr
  rw [show 1 + 2 * (m + 1) = 2 * m + 3 from by ring,
      show 2 * m + 3 + 2 * (m + 1) = 4 * m + 5 from by ring] at h_rearr
  apply stepStar_trans h_rearr
  -- R1 step
  have h_r1a : (⟨m + 1, 1, 2, 4 * m + 5, 0⟩ : Q) [fm]⊢ ⟨m + 2, 0, 1, 4 * m + 6, 0⟩ := by
    show fm ⟨m + 1, (0) + 1, (1) + 1, 4 * m + 5, 0⟩ = some _; rfl
  apply stepStar_trans (step_stepStar h_r1a)
  -- r3 chain
  have h_r3c := r3_chain (m + 2) 0 1 (4 * m + 6)
  simp only [Nat.zero_add] at h_r3c
  rw [show 1 + 2 * (m + 2) = 2 * m + 5 from by ring] at h_r3c
  apply stepStar_trans h_r3c
  -- R4 chain
  have h_r4 := r4_chain (2 * m + 3) (2 * m + 5) 0 0
  simp only [Nat.zero_add] at h_r4
  rw [show 2 * (2 * m + 3) = 4 * m + 6 from by ring] at h_r4
  apply stepStar_trans h_r4
  -- R5 step
  have h_r5 : (⟨0, 0, 2 * m + 5, 0, 2 * m + 3⟩ : Q) [fm]⊢ ⟨0, 2, 2 * m + 4, 0, 2 * m + 3⟩ := by
    show fm ⟨0, 0, (2 * m + 4) + 1, 0, 2 * m + 3⟩ = some _; rfl
  apply stepStar_trans (step_stepStar h_r5)
  -- Middle chain + R2 chain
  have h_mid := middle_chain (m + 2) 0 0 0 (m + 1)
  simp only [Nat.zero_add] at h_mid
  rw [show 2 * (m + 2) = 2 * m + 4 from by ring,
      show m + 1 + (m + 2) = 2 * m + 3 from by ring] at h_mid
  apply stepStar_trans h_mid
  have h_r2 := r2_chain (m + 1) 1 2 (2 * m + 4)
  rw [show 1 + (m + 1) = m + 2 from by ring,
      show 2 + 2 * (m + 1) = 2 * m + 4 from by ring] at h_r2
  exact h_r2

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨1, n + 2, 0, n + 2, 0⟩ [fm]⊢⁺ ⟨1, n + 3, 0, n + 3, 0⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    have h := cycle_even k
    rw [show k + k + 2 = 2 * k + 2 from by ring,
        show k + k + 3 = 2 * k + 3 from by ring]
    exact h
  · subst hk
    have h := cycle_odd k
    rw [show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
        show 2 * k + 1 + 3 = 2 * k + 4 from by ring]
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 2, 0, 2, 0⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨1, n + 2, 0, n + 2, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_290
