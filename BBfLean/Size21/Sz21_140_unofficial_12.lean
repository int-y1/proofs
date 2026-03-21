import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #12: [1/45, 98/5, 25/77, 3/7, 55/2]

Vector representation:
```
 0 -2 -1  0  0
 1  0 -1  2  0
 0  0  2 -1 -1
 0  1  0 -1  0
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_12

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R5+R1 chain: each pair does R5 then R1, consuming a by 1 and b by 2
theorem r5r1_chain : ∀ k, ∀ a b e, ⟨a+k, b+2*k, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
  step fm
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3+R2+R2 chain with b=0: each round R3, R2, R2
theorem r3r2r2_chain_b0 : ∀ E, ∀ A D, ⟨A, 0, 0, D+1, E⟩ [fm]⊢* ⟨A+2*E, 0, 0, D+1+3*E, 0⟩ := by
  intro E; induction' E with E ih <;> intro A D
  · exists 0
  rw [show D + 1 = D + 1 from rfl]
  step fm
  step fm
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3+R2+R2 chain with b=1: each round R3, R2, R2
theorem r3r2r2_chain_b1 : ∀ E, ∀ A D, ⟨A, 1, 0, D+1, E⟩ [fm]⊢* ⟨A+2*E, 1, 0, D+1+3*E, 0⟩ := by
  intro E; induction' E with E ih <;> intro A D
  · exists 0
  rw [show D + 1 = D + 1 from rfl]
  step fm
  step fm
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R4 chain: d → b
theorem r4_chain : ∀ d, ∀ a b, ⟨a, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+d, 0, 0, 0⟩ := by
  intro d; induction' d with d ih <;> intro a b
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Main transition for even b: (a+k+1, 2k, 0, 0, 0) ⊢⁺ (a+k+1+k+2, 3k+5, 0, 0, 0)
theorem main_trans_even (k a : ℕ) : ⟨a+k+1, 2*k, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+2*k+3, 3*k+5, 0, 0, 0⟩ := by
  -- Phase 1: R5+R1 chain: k pairs -> (a+1, 0, 0, 0, k)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 0, 0, k⟩)
  · have h := r5r1_chain k (a+1) 0 0
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase 2: R5 step -> (a, 0, 1, 0, k+1)
  apply step_stepStar_stepPlus (c₂ := ⟨a, 0, 1, 0, k+1⟩)
  · show fm ⟨a + 1, 0, 0, 0, k⟩ = some ⟨a, 0, 1, 0, k + 1⟩; simp [fm]
  -- Phase 3: R2 step -> (a+1, 0, 0, 2, k+1)
  apply stepStar_trans (c₂ := ⟨a+1, 0, 0, 2, k+1⟩)
  · have : ⟨a, 0, 1, 0, k+1⟩ [fm]⊢ ⟨a+1, 0, 0, 2, k+1⟩ := by
      show fm ⟨a, 0, 0+1, 0, k+1⟩ = some ⟨a+1, 0, 0, 0+2, k+1⟩; simp [fm]
    exact step_stepStar this
  -- Phase 4: R3+R2+R2 chain: (k+1) rounds
  apply stepStar_trans (c₂ := ⟨a+1+2*(k+1), 0, 0, 2+3*(k+1), 0⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring]
    exact r3r2r2_chain_b0 (k+1) (a+1) 1
  -- Phase 5: R4 chain
  apply stepStar_trans (c₂ := ⟨a+1+2*(k+1), 0+(2+3*(k+1)), 0, 0, 0⟩)
  · exact r4_chain (2+3*(k+1)) (a+1+2*(k+1)) 0
  ring_nf; finish

-- Main transition for odd b: (a+k+1, 2k+1, 0, 0, 0) ⊢⁺ (a+2*k+3, 3k+6, 0, 0, 0)
theorem main_trans_odd (k a : ℕ) : ⟨a+k+1, 2*k+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+2*k+3, 3*k+6, 0, 0, 0⟩ := by
  -- Phase 1: R5+R1 chain: k pairs -> (a+1, 1, 0, 0, k)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 1, 0, 0, k⟩)
  · have h := r5r1_chain k (a+1) 1 0
    simp only [Nat.zero_add] at h
    rw [show a + k + 1 = a + 1 + k from by ring,
        show 2 * k + 1 = 1 + 2 * k from by ring]
    exact h
  -- Phase 2: R5 step -> (a, 1, 1, 0, k+1)
  apply step_stepStar_stepPlus (c₂ := ⟨a, 1, 1, 0, k+1⟩)
  · show fm ⟨a + 1, 1, 0, 0, k⟩ = some ⟨a, 1, 1, 0, k + 1⟩; simp [fm]
  -- Phase 3: R2 step -> (a+1, 1, 0, 2, k+1)
  apply stepStar_trans (c₂ := ⟨a+1, 1, 0, 2, k+1⟩)
  · have : ⟨a, 1, 1, 0, k+1⟩ [fm]⊢ ⟨a+1, 1, 0, 2, k+1⟩ := by
      show fm ⟨a, 1, 0+1, 0, k+1⟩ = some ⟨a+1, 1, 0, 0+2, k+1⟩; simp [fm]
    exact step_stepStar this
  -- Phase 4: R3+R2+R2 chain: (k+1) rounds
  apply stepStar_trans (c₂ := ⟨a+1+2*(k+1), 1, 0, 2+3*(k+1), 0⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring]
    exact r3r2r2_chain_b1 (k+1) (a+1) 1
  -- Phase 5: R4 chain
  apply stepStar_trans (c₂ := ⟨a+1+2*(k+1), 1+(2+3*(k+1)), 0, 0, 0⟩)
  · exact r4_chain (2+3*(k+1)) (a+1+2*(k+1)) 1
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1, 0, 0, 0, 0) reaches (3, 5, 0, 0, 0) in 10 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 5, 0, 0, 0⟩) (by execute fm 10)
  -- Use progress_nonhalt with predicate
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a b, q = ⟨a, b, 0, 0, 0⟩ ∧ 2*a ≥ b + 1 ∧ b ≥ 5)
  · intro c ⟨a, b, hq, ha, hb⟩; subst hq
    rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- b = 2k (even case)
      rw [show k + k = 2 * k from by ring] at hk; subst hk
      have hak : a ≥ k + 1 := by omega
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + k + 1 := ⟨a - k - 1, by omega⟩
      refine ⟨⟨a'+2*k+3, 3*k+5, 0, 0, 0⟩, ⟨a'+2*k+3, 3*k+5, rfl, ?_, ?_⟩, main_trans_even k a'⟩
      · omega
      · omega
    · -- b = 2k+1 (odd case)
      rw [show 2 * k + 1 = 2 * k + 1 from rfl] at hk; subst hk
      have hak : a ≥ k + 1 := by omega
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + k + 1 := ⟨a - k - 1, by omega⟩
      refine ⟨⟨a'+2*k+3, 3*k+6, 0, 0, 0⟩, ⟨a'+2*k+3, 3*k+6, rfl, ?_, ?_⟩, main_trans_odd k a'⟩
      · omega
      · omega
  · exact ⟨3, 5, rfl, by omega, by omega⟩
