import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #900: [4/15, 3/14, 275/2, 49/11, 22/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0  0  2 -1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_900

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R2 chain: move d to b. c=0 so R1 doesn't fire.
theorem d_to_b : ∀ k, ∀ b d, ⟨a + k, b, 0, d + k, e⟩ [fm]⊢* ⟨a, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1) (d := d))
    ring_nf; finish

-- Mix chain: k rounds of (R3, R1, R1), consuming 2 from b per round.
theorem mix_chain : ∀ k, ∀ a b e, ⟨a + 1, b + 2 * k, 0, 0, e⟩ [fm]⊢* ⟨a + 3 * k + 1, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 3) (b := b) (e := e + 1))
    ring_nf; finish

-- Odd tail after mix_chain when b=1 remains.
theorem mix_odd_tail : ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢* ⟨a + 2, 0, 1, 0, e + 1⟩ := by
  step fm; step fm; finish

-- R3 chain: convert a to c and e. b=0, d=0.
theorem r3_chain : ∀ k, ∀ a₀ c₀ e₀, ⟨a₀ + k, 0, c₀, 0, e₀⟩ [fm]⊢* ⟨a₀, 0, c₀ + 2 * k, 0, e₀ + k⟩ := by
  intro k; induction' k with k ih <;> intro a₀ c₀ e₀
  · exists 0
  · rw [show a₀ + (k + 1) = (a₀ + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a₀ := a₀) (c₀ := c₀ + 2) (e₀ := e₀ + 1))
    ring_nf; finish

-- R4 chain: convert e to d. a=0, b=0.
theorem r4_chain : ∀ k, ∀ c₀ d₀ e₀, ⟨0, 0, c₀, d₀, e₀ + k⟩ [fm]⊢* ⟨0, 0, c₀, d₀ + 2 * k, e₀⟩ := by
  intro k; induction' k with k ih <;> intro c₀ d₀ e₀
  · exists 0
  · rw [show e₀ + (k + 1) = (e₀ + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c₀ := c₀) (d₀ := d₀ + 2) (e₀ := e₀))
    ring_nf; finish

-- Spiral R2+R1 pairs.
theorem spiral_pairs : ∀ c₀, ∀ n d, ⟨n + 1, 0, c₀, d + c₀, 1⟩ [fm]⊢* ⟨n + c₀ + 1, 0, 0, d, 1⟩ := by
  intro c₀; induction' c₀ with c₀ ih <;> intro n d
  · exists 0
  · rw [show d + (c₀ + 1) = (d + c₀) + 1 from by ring]
    step fm; step fm
    rw [show n + 2 = (n + 1) + 1 from by ring]
    apply stepStar_trans (ih (n := n + 1) (d := d))
    ring_nf; finish

-- Full spiral: R5 then spiral_pairs.
theorem full_spiral (C D : ℕ) : ⟨0, 0, C + 1, D + C, 0⟩ [fm]⊢⁺ ⟨C + 1, 0, 0, D, 1⟩ := by
  step fm
  apply stepStar_trans (spiral_pairs C (n := 0) (d := D))
  ring_nf; finish

-- Phases 1-4 composed: from (A, 0, 0, D, 1) to (0, 0, C, D', 0)
-- For even D = 2*(K+1): goes through mix_chain then r3_chain then r4_chain.
-- For odd D = 2*K+1: additionally uses mix_odd_tail.

-- Even case.
theorem main_even (K : ℕ) :
    ⟨m + 2 * (K + 1) + 1, 0, 0, 2 * (K + 1), 1⟩ [fm]⊢⁺
    ⟨2 * m + 6 * (K + 1) + 2, 0, 0, 2 * (K + 1) + 3, 1⟩ := by
  -- Phase 1: d_to_b 2*(K+1)
  have h1 := d_to_b (2 * K + 2) (a := m + 1) (b := 0) (d := 0) (e := 1)
  simp only [Nat.zero_add] at h1
  -- h1 : (m + 1 + (2*K+2), 0, 0, 2*K+2, 1) ⊢* (m+1, 2*K+2, 0, 0, 1)
  -- Phase 2: mix_chain (K+1)
  have h2 := mix_chain (K + 1) (a := m) (b := 0) (e := 1)
  simp only [Nat.zero_add] at h2
  -- h2 : (m+1, 2*(K+1), 0, 0, 1) ⊢* (m+3*(K+1)+1, 0, 0, 0, 1+(K+1))
  -- Phase 3: r3_chain
  have h3 := r3_chain (m + 3 * K + 4) (a₀ := 0) (c₀ := 0) (e₀ := K + 2)
  simp only [Nat.zero_add] at h3
  -- h3 : (m+3K+4, 0, 0, 0, K+2) ⊢* (0, 0, 2*(m+3K+4), 0, K+2+m+3K+4)
  -- Phase 4: r4_chain
  have h4 := r4_chain (m + 4 * K + 6) (c₀ := 2 * m + 6 * K + 8) (d₀ := 0) (e₀ := 0)
  simp only [Nat.zero_add] at h4
  -- h4 : (0, 0, 2m+6K+8, 0, m+4K+6) ⊢* (0, 0, 2m+6K+8, 2(m+4K+6), 0)
  -- Phase 5: full_spiral
  have h5 := full_spiral (2 * m + 6 * K + 7) (2 * (K + 1) + 3)
  -- Compose
  apply stepStar_stepPlus_stepPlus
  · rw [show m + 2 * (K + 1) + 1 = m + 1 + (2 * K + 2) from by ring,
        show 2 * (K + 1) = 2 * K + 2 from by ring]
    exact h1
  apply stepStar_stepPlus_stepPlus
  · rw [show (2 * K + 2 : ℕ) = 2 * (K + 1) from by ring]; exact h2
  apply stepStar_stepPlus_stepPlus
  · rw [show m + 3 * (K + 1) + 1 = m + 3 * K + 4 from by ring,
        show 1 + (K + 1) = K + 2 from by ring]; exact h3
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * (m + 3 * K + 4) = 2 * m + 6 * K + 8 from by ring,
        show K + 2 + (m + 3 * K + 4) = m + 4 * K + 6 from by ring]; exact h4
  rw [show 2 * (m + 4 * K + 6) = 2 * m + 8 * K + 12 from by ring,
      show 2 * m + 6 * K + 8 = (2 * m + 6 * K + 7) + 1 from by ring,
      show 2 * m + 8 * K + 12 = (2 * (K + 1) + 3) + (2 * m + 6 * K + 7) from by ring,
      show 2 * m + 6 * K + 7 + 1 = 2 * m + 6 * (K + 1) + 2 from by ring]
  exact h5

-- Odd case.
theorem main_odd (K : ℕ) :
    ⟨m + 2 * K + 2, 0, 0, 2 * K + 1, 1⟩ [fm]⊢⁺
    ⟨2 * m + 6 * K + 5, 0, 0, 2 * K + 4, 1⟩ := by
  -- Phase 1: d_to_b (2*K+1)
  have h1 := d_to_b (2 * K + 1) (a := m + 1) (b := 0) (d := 0) (e := 1)
  simp only [Nat.zero_add] at h1
  -- Phase 2a: mix_chain K with b=1
  have h2 := mix_chain K (a := m) (b := 1) (e := 1)
  -- Phase 2b: mix_odd_tail
  have h3 := mix_odd_tail (a := m + 3 * K) (e := 1 + K)
  -- Phase 3: r3_chain
  have h4 := r3_chain (m + 3 * K + 2) (a₀ := 0) (c₀ := 1) (e₀ := K + 2)
  simp only [Nat.zero_add] at h4
  -- Phase 4: r4_chain
  have h5 := r4_chain (m + 4 * K + 4) (c₀ := 2 * m + 6 * K + 5) (d₀ := 0) (e₀ := 0)
  simp only [Nat.zero_add] at h5
  -- Phase 5: full_spiral
  have h6 := full_spiral (2 * m + 6 * K + 4) (2 * K + 4)
  -- Compose
  apply stepStar_stepPlus_stepPlus
  · rw [show m + 2 * K + 2 = m + 1 + (2 * K + 1) from by ring,
        show 2 * K + 1 = 2 * K + 1 from rfl]
    exact h1
  apply stepStar_stepPlus_stepPlus
  · rw [show (2 * K + 1 : ℕ) = 1 + 2 * K from by ring]; exact h2
  apply stepStar_stepPlus_stepPlus
  · rw [show m + 3 * K + 1 = (m + 3 * K) + 1 from by ring]; exact h3
  apply stepStar_stepPlus_stepPlus
  · rw [show m + 3 * K + 2 = m + 3 * K + 2 from rfl,
        show 1 + K + 1 = K + 2 from by ring]; exact h4
  apply stepStar_stepPlus_stepPlus
  · rw [show 1 + 2 * (m + 3 * K + 2) = 2 * m + 6 * K + 5 from by ring,
        show K + 2 + (m + 3 * K + 2) = m + 4 * K + 4 from by ring]; exact h5
  rw [show 2 * (m + 4 * K + 4) = 2 * m + 8 * K + 8 from by ring,
      show 2 * m + 6 * K + 5 = (2 * m + 6 * K + 4) + 1 from by ring,
      show 2 * m + 8 * K + 8 = (2 * K + 4) + (2 * m + 6 * K + 4) from by ring]
  exact h6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 1⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 1⟩ ∧ a ≥ d + 1 ∧ d ≥ 1)
  · intro c ⟨a, d, hq, ha, hd⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨m', rfl⟩ : ∃ m', a = m' + 2 * (k + 1) + 1 := ⟨a - 2 * (k + 1) - 1, by omega⟩
      exact ⟨⟨2 * m' + 6 * (k + 1) + 2, 0, 0, 2 * (k + 1) + 3, 1⟩,
        ⟨2 * m' + 6 * (k + 1) + 2, 2 * (k + 1) + 3, rfl, by omega, by omega⟩,
        main_even k⟩
    · subst hK
      obtain ⟨m', rfl⟩ : ∃ m', a = m' + 2 * K + 2 := ⟨a - 2 * K - 2, by omega⟩
      exact ⟨⟨2 * m' + 6 * K + 5, 0, 0, 2 * K + 4, 1⟩,
        ⟨2 * m' + 6 * K + 5, 2 * K + 4, rfl, by omega, by omega⟩,
        main_odd K⟩
  · exact ⟨2, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_900
