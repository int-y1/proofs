import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #17: [1/135, 14/15, 9/7, 125/2, 3/5]

Vector representation:
```
 0 -3 -1  0
 1 -1 -1  1
 0  2  0 -1
-1  0  3  0
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_17

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+3, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4 chain: (a+k, 0, c, 0) ⊢* (a, 0, c+3*k, 0)
theorem r4_chain : ∀ k, ∀ a c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+3*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a (c + 3)); ring_nf; finish

-- R3 chain with c=0: (a, b, 0, k) ⊢* (a, b+2*k, 0, 0)
theorem r3_chain : ∀ k, ∀ a b, ⟨a, b, 0, k⟩ [fm]⊢* ⟨a, b+2*k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  step fm
  apply stepStar_trans (ih a (b + 2)); ring_nf; finish

-- Single rising step: (a, 0, c+2, d+1) ⊢* (a+2, 0, c, d+2)
theorem rise_step : ∀ a c d, ⟨a, 0, c+2, d+1⟩ [fm]⊢* ⟨a+2, 0, c, d+2⟩ := by
  intro a c d
  step fm  -- R3
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm  -- R2
  step fm  -- R2
  finish

-- Rise core: k iterations
theorem rise_core : ∀ k, ∀ a c d, ⟨a, 0, c+2*k, d+1⟩ [fm]⊢* ⟨a+2*k, 0, c, d+k+1⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  apply stepStar_trans (rise_step a (c + 2 * k) d)
  apply stepStar_trans (ih (a + 2) c (d + 1)); ring_nf; finish

-- Rise even: (0, 0, 2*(m+1), 0) ⊢* (2*m+1, 2*(m+1), 0, 0)
theorem rise_even (m : ℕ) : ⟨0, 0, 2*(m+1), 0⟩ [fm]⊢* ⟨2*m+1, 2*(m+1), 0, 0⟩ := by
  rw [show 2 * (m + 1) = (2 * m) + 1 + 1 from by ring]
  step fm  -- R5
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm  -- R2: (1, 0, 2*m, 1)
  rw [show 2 * m = 0 + 2 * m from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (rise_core m 1 0 0)
  rw [show 0 + m + 1 = m + 1 from by ring]
  apply stepStar_trans (r3_chain (m+1) (1+2*m) 0)
  ring_nf; finish

-- Rise odd: (0, 0, 2*m+3, 0) ⊢* (2*m+2, 2*m+3, 0, 0)
theorem rise_odd (m : ℕ) : ⟨0, 0, 2*m+3, 0⟩ [fm]⊢* ⟨2*m+2, 2*m+3, 0, 0⟩ := by
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
  step fm  -- R5
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm  -- R2: (1, 0, 2*m+1, 1)
  rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (rise_core m 1 1 0)
  rw [show 0 + m + 1 = m + 1 from by ring]
  step fm  -- R3: (1+2*m, 2, 1, m)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm  -- R2: (1+2*m+1, 1, 0, m+1)
  rw [show 1 + 2 * m + 1 = 2 + 2 * m from by ring]
  apply stepStar_trans (r3_chain (m+1) (2+2*m) 1)
  ring_nf; finish

-- Rise plus: (0, 0, c+2, 0) ⊢⁺ (c+1, c+2, 0, 0)
theorem rise_plus : ∀ c, ⟨0, 0, c+2, 0⟩ [fm]⊢⁺ ⟨c+1, c+2, 0, 0⟩ := by
  intro c
  rw [show c + 2 = (c + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (c+1)+1, 0⟩ = some ⟨0, 1, c+1, 0⟩; simp [fm]
  rw [show c + 1 = c + 1 from rfl]
  -- After R5: (0, 1, c+1, 0). R2: (1, 0, c, 1).
  step fm  -- R2
  -- (1, 0, c, 1). Split on parity of c.
  rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m = 0 + 2 * m from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (rise_core m 1 0 0)
    rw [show 0 + m + 1 = m + 1 from by ring]
    apply stepStar_trans (r3_chain (m+1) (1+2*m) 0)
    ring_nf; finish
  · subst hm
    rw [show 2 * m + 1 = 1 + 2 * m from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (rise_core m 1 1 0)
    rw [show 0 + m + 1 = m + 1 from by ring]
    step fm  -- R3
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm  -- R2
    rw [show 1 + 2 * m + 1 = 2 + 2 * m from by ring]
    apply stepStar_trans (r3_chain (m+1) (2+2*m) 1)
    ring_nf; finish

-- Drain 9: (a+1, b+9, 0, 0) ⊢* (a, b, 0, 0)
theorem drain_9 : ∀ a b, ⟨a+1, b+9, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  intro a b
  step fm  -- R4: (a, b+9, 3, 0)
  rw [show b + 9 = (b + 6) + 3 from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  step fm  -- R1
  rw [show b + 6 = (b + 3) + 3 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm  -- R1
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm  -- R1
  finish

-- Drain chain: k steps
theorem drain_chain : ∀ k, ∀ a b, ⟨a+k, b+9*k, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + 9 * (k + 1) = (b + 9 * k) + 9 from by ring]
  apply stepStar_trans (drain_9 (a + k) (b + 9 * k))
  exact ih a b

-- b8 to b3
theorem b8_to_b3 : ∀ a, ⟨a+1, 8, 0, 0⟩ [fm]⊢* ⟨a+1, 3, 0, 0⟩ := by
  intro a; step fm; step fm; step fm; step fm; step fm; finish

-- b5 to b3
theorem b5_to_b3 : ∀ a, ⟨a+1, 5, 0, 0⟩ [fm]⊢* ⟨a+3, 3, 0, 0⟩ := by
  intro a
  step fm; step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm; step fm
  finish

-- b2 to b3
theorem b2_to_b3 : ∀ a, ⟨a+1, 2, 0, 0⟩ [fm]⊢* ⟨a+5, 3, 0, 0⟩ := by
  intro a
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (b5_to_b3 (a + 2)); ring_nf; finish

-- b3 exit + dump: (a+1, 3, 0, 0) ⊢* (0, 0, 3*a+2, 0)
theorem b3_exit : ∀ a, ⟨a+1, 3, 0, 0⟩ [fm]⊢* ⟨0, 0, 3*a+2, 0⟩ := by
  intro a
  step fm; step fm  -- (a, 0, 2, 0)
  have h := r4_chain a 0 2
  rw [show 0 + a = a from by ring] at h
  apply stepStar_trans h; ring_nf; finish

-- Full cycle for c mod 9 = 2 (c = 9k+11, k >= 0):
-- (0, 0, 9k+11, 0) ⊢⁺ (0, 0, 24k+38, 0)
theorem main_mod2 (k : ℕ) :
    ⟨0, 0, 9*k+11, 0⟩ [fm]⊢⁺ ⟨0, 0, 24*k+38, 0⟩ := by
  rw [show 9 * k + 11 = (9 * k + 9) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (c₂ := ⟨9*k+10, 9*k+11, 0, 0⟩)
  · have h := rise_plus (9*k+9)
    rw [show (9 * k + 9) + 1 = 9 * k + 10 from by ring,
        show (9 * k + 9) + 2 = 9 * k + 11 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨8*k+9, 2, 0, 0⟩)
  · rw [show 9 * k + 10 = (8 * k + 9) + (k + 1) from by ring,
        show 9 * k + 11 = 2 + 9 * (k + 1) from by ring]
    exact drain_chain (k+1) (8*k+9) 2
  apply stepStar_trans (c₂ := ⟨8*k+13, 3, 0, 0⟩)
  · rw [show 8 * k + 9 = (8 * k + 8) + 1 from by ring]
    apply stepStar_trans (b2_to_b3 (8*k+8)); ring_nf; finish
  have h := b3_exit (8*k+12)
  rw [show 8 * k + 13 = (8 * k + 12) + 1 from by ring,
      show 3 * (8 * k + 12) + 2 = 24 * k + 38 from by ring] at *
  exact h

-- Full cycle for c mod 9 = 5 (c = 9k+5, k >= 0):
theorem main_mod5 (k : ℕ) :
    ⟨0, 0, 9*k+5, 0⟩ [fm]⊢⁺ ⟨0, 0, 24*k+17, 0⟩ := by
  rw [show 9 * k + 5 = (9 * k + 3) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (c₂ := ⟨9*k+4, 9*k+5, 0, 0⟩)
  · have h := rise_plus (9*k+3)
    rw [show (9 * k + 3) + 1 = 9 * k + 4 from by ring,
        show (9 * k + 3) + 2 = 9 * k + 5 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨8*k+4, 5, 0, 0⟩)
  · rw [show 9 * k + 4 = (8 * k + 4) + k from by ring,
        show 9 * k + 5 = 5 + 9 * k from by ring]
    exact drain_chain k (8*k+4) 5
  apply stepStar_trans (c₂ := ⟨8*k+6, 3, 0, 0⟩)
  · rw [show 8 * k + 4 = (8 * k + 3) + 1 from by ring]
    apply stepStar_trans (b5_to_b3 (8*k+3)); ring_nf; finish
  have h := b3_exit (8*k+5)
  rw [show 8 * k + 6 = (8 * k + 5) + 1 from by ring,
      show 3 * (8 * k + 5) + 2 = 24 * k + 17 from by ring] at *
  exact h

-- Full cycle for c mod 9 = 8 (c = 9k+8, k >= 0):
theorem main_mod8 (k : ℕ) :
    ⟨0, 0, 9*k+8, 0⟩ [fm]⊢⁺ ⟨0, 0, 24*k+20, 0⟩ := by
  rw [show 9 * k + 8 = (9 * k + 6) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (c₂ := ⟨9*k+7, 9*k+8, 0, 0⟩)
  · have h := rise_plus (9*k+6)
    rw [show (9 * k + 6) + 1 = 9 * k + 7 from by ring,
        show (9 * k + 6) + 2 = 9 * k + 8 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨8*k+7, 8, 0, 0⟩)
  · rw [show 9 * k + 7 = (8 * k + 7) + k from by ring,
        show 9 * k + 8 = 8 + 9 * k from by ring]
    exact drain_chain k (8*k+7) 8
  apply stepStar_trans (c₂ := ⟨8*k+7, 3, 0, 0⟩)
  · rw [show 8 * k + 7 = (8 * k + 6) + 1 from by ring]
    apply stepStar_trans (b8_to_b3 (8*k+6)); ring_nf; finish
  have h := b3_exit (8*k+6)
  rw [show 8 * k + 7 = (8 * k + 6) + 1 from by ring,
      show 3 * (8 * k + 6) + 2 = 24 * k + 20 from by ring] at *
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 0⟩) (by execute fm 9)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c, q = ⟨0, 0, c, 0⟩ ∧ c ≥ 5 ∧ c % 3 = 2)
  · intro q ⟨c, hq, hc5, hcmod⟩; subst hq
    have hmod9 : c % 9 = 2 ∨ c % 9 = 5 ∨ c % 9 = 8 := by omega
    rcases hmod9 with h | h | h
    · have ⟨j, hj⟩ : ∃ j, c = 9 * j + 2 := ⟨c / 9, by omega⟩
      have hj1 : j ≥ 1 := by omega
      have ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      subst hj; subst hk
      refine ⟨⟨0, 0, 24*k+38, 0⟩, ⟨24*k+38, rfl, by omega, by omega⟩, ?_⟩
      rw [show 9 * (k + 1) + 2 = 9 * k + 11 from by ring]; exact main_mod2 k
    · have ⟨j, hj⟩ : ∃ j, c = 9 * j + 5 := ⟨c / 9, by omega⟩
      subst hj
      exact ⟨⟨0, 0, 24*j+17, 0⟩, ⟨24*j+17, rfl, by omega, by omega⟩, main_mod5 j⟩
    · have ⟨j, hj⟩ : ∃ j, c = 9 * j + 8 := ⟨c / 9, by omega⟩
      subst hj
      exact ⟨⟨0, 0, 24*j+20, 0⟩, ⟨24*j+20, rfl, by omega, by omega⟩, main_mod8 j⟩
  · exact ⟨5, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_17
