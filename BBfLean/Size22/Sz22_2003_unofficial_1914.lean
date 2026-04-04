import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1914: [9/385, 50/7, 7/15, 11/2, 49/11]

Vector representation:
```
 0  2 -1 -1 -1
 1  0  2 -1  0
 0 -1 -1  1  0
-1  0  0  0  1
 0  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1914

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | _ => none

-- R4 chain: (a + k, 0, c, 0, e) ⊢* (a, 0, c, 0, e + k)
theorem a_to_e : ∀ k, ∀ a e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    apply stepStar_trans (step_stepStar (by simp [fm] : ⟨(a + k) + 1, 0, c, 0, e⟩ [fm]⊢ ⟨a + k, 0, c, 0, e + 1⟩))
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

-- R4 chain with stepPlus: (a + k + 1, 0, c, 0, e) ⊢⁺ (a, 0, c, 0, e + k + 1)
theorem a_to_e_plus : ⟨a + k + 1, 0, c, 0, e⟩ [fm]⊢⁺ ⟨a, 0, c, 0, e + k + 1⟩ := by
  rw [show a + k + 1 = (a + k) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨a + k, 0, c, 0, e + 1⟩) (by simp [fm])
  apply stepStar_trans (a_to_e k a (e + 1))
  ring_nf; finish

-- R3+R1 interleave chain
theorem interleave_chain : ∀ k, ∀ b c e, ⟨0, b + 1, c + 2 * k, 0, e + k⟩ [fm]⊢* ⟨0, b + k + 1, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b := b + 1) c e)
    ring_nf; finish

-- Tail drain step: (0, b, 0, 0, e+4) ⊢* (0, b+2, 0, 0, e+3)
theorem tail_drain_step : ⟨0, b, 0, 0, e + 4⟩ [fm]⊢* ⟨0, b + 2, 0, 0, e + 3⟩ := by
  execute fm 9

-- Tail drain base: (0, b, 0, 0, 3) ⊢* (2, b+2, 0, 0, 0)
theorem tail_drain_base : ⟨0, b, 0, 0, 3⟩ [fm]⊢* ⟨2, b + 2, 0, 0, 0⟩ := by
  execute fm 7

-- Tail drain: (0, b, 0, 0, e+3) ⊢* (2, b+2*(e+1), 0, 0, 0)
theorem tail_drain : ∀ e, ∀ b, ⟨0, b, 0, 0, e + 3⟩ [fm]⊢* ⟨2, b + 2 * (e + 1), 0, 0, 0⟩ := by
  intro e; induction' e with e ih <;> intro b
  · apply stepStar_trans tail_drain_base; ring_nf; finish
  · apply stepStar_trans tail_drain_step
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

-- Odd bridge: (0, b+1, 0, 1, e+1) ⊢* (0, b+2, 0, 0, e+1)
theorem odd_bridge : ⟨0, b + 1, 0, 1, e + 1⟩ [fm]⊢* ⟨0, b + 2, 0, 0, e + 1⟩ := by
  execute fm 4

-- Closing: (2, B, 0, 0, 0) ⊢* (2, B+1, 2, 0, 0)
theorem closing : ⟨2, B, 0, 0, 0⟩ [fm]⊢* ⟨2, B + 1, 2, 0, 0⟩ := by
  execute fm 7

-- Spiral: R3+R2 chain
theorem spiral : ∀ k, ∀ a c, ⟨a, k, c + 1, 0, 0⟩ [fm]⊢* ⟨a + k, 0, c + k + 1, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (c := c + 1))
    ring_nf; finish

-- Even macro: (2*m+10, 0, 2*m+10, 0, 0) ⊢⁺ (3*m+13, 0, 3*m+13, 0, 0)
theorem main_even : ⟨2 * m + 10, 0, 2 * m + 10, 0, 0⟩ [fm]⊢⁺ ⟨3 * m + 13, 0, 3 * m + 13, 0, 0⟩ := by
  -- Phase 1: a_to_e_plus
  rw [show (2 * m + 10 : ℕ) = 0 + (2 * m + 9) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (a_to_e_plus (a := 0) (k := 2 * m + 9) (e := 0) (c := 0 + (2 * m + 9) + 1))
  rw [show 0 + (2 * m + 9) + 1 = 2 * m + 10 from by ring]
  -- At (0, 0, 2*m+10, 0, 2*m+10)
  -- Phase 2: R5+R1+R1
  step fm; step fm; step fm
  -- At (0, 4, 2*m+8, 0, 2*m+7)
  -- Phase 3: interleave with k=m+4
  rw [show 2 * m + 8 = 0 + 2 * (m + 4) from by ring,
      show 2 * m + 7 = (m + 3) + (m + 4) from by ring]
  apply stepStar_trans (interleave_chain (m + 4) (b := 3) 0 (m + 3))
  rw [show 3 + (m + 4) + 1 = m + 8 from by ring]
  -- At (0, m+8, 0, 0, m+3)
  -- Phase 4: tail_drain
  apply stepStar_trans (tail_drain m (b := m + 8))
  rw [show m + 8 + 2 * (m + 1) = 3 * m + 10 from by ring]
  -- Phase 5: closing + spiral
  apply stepStar_trans (closing (B := 3 * m + 10))
  rw [show 3 * m + 10 + 1 = 3 * m + 11 from by ring]
  apply stepStar_trans (spiral (3 * m + 11) (a := 2) (c := 1))
  ring_nf; finish

-- Odd macro: (2*m+9, 0, 2*m+9, 0, 0) ⊢⁺ (3*m+12, 0, 3*m+12, 0, 0)
theorem main_odd : ⟨2 * m + 9, 0, 2 * m + 9, 0, 0⟩ [fm]⊢⁺ ⟨3 * m + 12, 0, 3 * m + 12, 0, 0⟩ := by
  -- Phase 1: a_to_e_plus
  rw [show (2 * m + 9 : ℕ) = 0 + (2 * m + 8) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (a_to_e_plus (a := 0) (k := 2 * m + 8) (e := 0) (c := 0 + (2 * m + 8) + 1))
  rw [show 0 + (2 * m + 8) + 1 = 2 * m + 9 from by ring]
  -- At (0, 0, 2*m+9, 0, 2*m+9)
  -- Phase 2: R5+R1+R1
  step fm; step fm; step fm
  -- At (0, 4, 2*m+7, 0, 2*m+6)
  -- Phase 3: interleave with k=m+3, then R3
  rw [show 2 * m + 7 = 1 + 2 * (m + 3) from by ring,
      show 2 * m + 6 = (m + 3) + (m + 3) from by ring]
  apply stepStar_trans (interleave_chain (m + 3) (b := 3) 1 (m + 3))
  rw [show 3 + (m + 3) + 1 = m + 7 from by ring]
  -- At (0, m+7, 1, 0, m+3)
  -- R3 to clear c=1
  step fm
  -- At (0, m+6, 0, 1, m+3)
  -- Phase 4: odd_bridge
  rw [show m + 6 = (m + 5) + 1 from by ring,
      show m + 3 = (m + 2) + 1 from by ring]
  apply stepStar_trans (odd_bridge (b := m + 5) (e := m + 2))
  rw [show (m + 5) + 2 = m + 7 from by ring,
      show (m + 2) + 1 = m + 3 from by ring]
  -- At (0, m+7, 0, 0, m+3)
  -- Phase 5: tail_drain
  apply stepStar_trans (tail_drain m (b := m + 7))
  rw [show m + 7 + 2 * (m + 1) = 3 * m + 9 from by ring]
  -- Phase 6: closing + spiral
  apply stepStar_trans (closing (B := 3 * m + 9))
  rw [show 3 * m + 9 + 1 = 3 * m + 10 from by ring]
  apply stepStar_trans (spiral (3 * m + 10) (a := 2) (c := 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨11, 0, 11, 0, 0⟩) (by execute fm 185)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨n, 0, n, 0, 0⟩ ∧ n ≥ 9)
  · intro c ⟨n, hq, hn⟩; subst hq
    rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 5 := ⟨K - 5, by omega⟩
      refine ⟨⟨3 * m + 13, 0, 3 * m + 13, 0, 0⟩, ⟨3 * m + 13, rfl, by omega⟩, ?_⟩
      exact main_even
    · subst hK
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 4 := ⟨K - 4, by omega⟩
      refine ⟨⟨3 * m + 12, 0, 3 * m + 12, 0, 0⟩, ⟨3 * m + 12, rfl, by omega⟩, ?_⟩
      show ⟨2 * (m + 4) + 1, 0, 2 * (m + 4) + 1, 0, 0⟩ [fm]⊢⁺ _
      rw [show 2 * (m + 4) + 1 = 2 * m + 9 from by ring]
      exact main_odd
  · exact ⟨11, rfl, by omega⟩
