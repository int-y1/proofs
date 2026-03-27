import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #59: [1/15, 98/3, 27/77, 5/49, 33/2]

Vector representation:
```
 0 -1 -1  0  0
 1 -1  0  2  0
 0  3  0 -1 -1
 0  0  1 -2  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_59

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R3+3xR2 chain: (a, 0, 0, d+1, e+k+1) ⊢* (a+3k+3, 0, 0, d+5k+6, e)
theorem r3r2_chain : ∀ k, ∀ a d e,
    ⟨a, 0, 0, d + 1, e + k + 1⟩ [fm]⊢* ⟨a + 3 * k + 3, 0, 0, d + 5 * k + 6, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · step fm; step fm; step fm; step fm; ring_nf; finish
  rw [show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring,
      show d + 1 + 0 = d + 1 from by ring]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (ih (a + 3) (d + 5) e)
  ring_nf; finish

-- R4 chain: (a, 0, c, d + 2*k, 0) ⊢* (a, 0, c+k, d, 0)
theorem r4_chain : ∀ k, ∀ a c d,
    ⟨a, 0, c, d + 2 * k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · simp; exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
  step fm
  apply stepStar_trans (ih a (c + 1) d)
  ring_nf; finish

-- R5+R1 chain: (a+k, 0, k, 0, e) ⊢* (a, 0, 0, 0, e+k)
theorem r5r1_chain : ∀ k, ∀ a e,
    ⟨a + k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · simp; exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih a (e + 1))
  ring_nf; finish

-- Phase 1: (a+1, 0, 0, 0, e+1) ⊢* (a+3e+7, 0, 0, 5e+12, 0)
theorem phase1 (a e : ℕ) :
    ⟨a + 1, 0, 0, 0, e + 1⟩ [fm]⊢* ⟨a + 3 * e + 7, 0, 0, 5 * e + 12, 0⟩ := by
  step fm; step fm
  rw [show e + 1 + 1 = 0 + (e + 1) + 1 from by ring]
  apply stepStar_trans (r3r2_chain (e + 1) (a + 1) 1 0)
  ring_nf; finish

-- Phase 2 (even D): R4 chain then R5+R1 chain
theorem phase2_even (a m : ℕ) :
    ⟨a + m + 1, 0, 0, 2 * m + 2, 0⟩ [fm]⊢* ⟨a, 0, 0, 0, m + 1⟩ := by
  rw [show 2 * m + 2 = 0 + 2 * (m + 1) from by ring]
  apply stepStar_trans (r4_chain (m + 1) (a + m + 1) 0 0)
  rw [show (0 : ℕ) + (m + 1) = m + 1 from by ring,
      show a + m + 1 = a + (m + 1) from by ring]
  have h := r5r1_chain (m + 1) a 0
  rw [show (0 : ℕ) + (m + 1) = m + 1 from by ring] at h
  exact h

-- Phase 2 (odd D): R4 chain, 6 fixed steps, then R5+R1 chain
theorem phase2_odd (a k : ℕ) :
    ⟨a + k + 5, 0, 0, 2 * k + 9, 0⟩ [fm]⊢* ⟨a + 4, 0, 0, 0, k⟩ := by
  rw [show 2 * k + 9 = 1 + 2 * (k + 4) from by ring]
  apply stepStar_trans (r4_chain (k + 4) (a + k + 5) 0 1)
  rw [show (0 : ℕ) + (k + 4) = k + 4 from by ring,
      show a + k + 5 = (a + k + 4) + 1 from by ring]
  step fm
  rw [show k + 4 = (k + 3) + 1 from by ring]
  step fm; step fm
  rw [show k + 3 = (k + 2) + 1 from by ring]
  step fm
  rw [show k + 2 = (k + 1) + 1 from by ring]
  step fm; step fm
  rw [show a + k + 4 = (a + 4) + k from by ring]
  have h := r5r1_chain k (a + 4) 0
  rw [show (0 : ℕ) + k = k from by ring] at h
  exact h

-- Main transition for odd e
theorem main_odd (a k : ℕ) :
    ⟨a + 1, 0, 0, 0, 2 * k + 1⟩ [fm]⊢⁺ ⟨a + k + 1, 0, 0, 0, 5 * k + 6⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨a, 0 + 1, 0, 0, 2 * k + 1 + 1⟩)
  · rfl
  step fm
  -- State: (a+1, 0, 0, 2, 2k+2). Need to rw 2 = 1+1 for the d+1 pattern.
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * k + 1 + 1 = 0 + (2 * k + 1) + 1 from by ring]
  apply stepStar_trans (r3r2_chain (2 * k + 1) (a + 1) 1 0)
  have h := phase2_even (a + k + 1) (5 * k + 5)
  convert h using 2; ring_nf

-- Main transition for even e
theorem main_even (a k : ℕ) :
    ⟨a + 1, 0, 0, 0, 2 * k + 2⟩ [fm]⊢⁺ ⟨a + k + 5, 0, 0, 0, 5 * k + 4⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨a, 0 + 1, 0, 0, 2 * k + 2 + 1⟩)
  · rfl
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * k + 2 + 1 = 0 + (2 * k + 2) + 1 from by ring]
  apply stepStar_trans (r3r2_chain (2 * k + 2) (a + 1) 1 0)
  have h := phase2_odd (a + k + 1) (5 * k + 4)
  convert h using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 18)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1 ∧ e ≥ 1)
  · intro c ⟨a, e, hq, ha, he⟩; subst hq
    rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- e = 2K, even, K >= 1 since e >= 1 and even
      have hK1 : K ≥ 1 := by omega
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      subst hK
      refine ⟨⟨a' + K' + 5, 0, 0, 0, 5 * K' + 4⟩,
        ⟨a' + K' + 5, 5 * K' + 4, rfl, by omega, by omega⟩, ?_⟩
      have h := main_even a' K'
      convert h using 2; ring_nf
    · -- e = 2K+1, odd
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      subst hK
      refine ⟨⟨a' + K + 1, 0, 0, 0, 5 * K + 6⟩,
        ⟨a' + K + 1, 5 * K + 6, rfl, by omega, by omega⟩,
        main_odd a' K⟩
  · exact ⟨3, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_59
