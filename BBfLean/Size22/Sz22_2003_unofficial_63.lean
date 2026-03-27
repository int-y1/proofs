import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #63: [1/15, 98/3, 9/77, 5/7, 847/2]

Vector representation:
```
 0 -1 -1  0  0
 1 -1  0  2  0
 0  2  0 -1 -1
 0  0  1 -1  0
-1  0  0  1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_63

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | _ => none

-- R4 repeated: d → c
theorem d_to_c : ∀ k : ℕ, ∀ a c d, ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3+R2+R2 inner loop: drains e while building a and d
theorem inner_loop : ∀ k : ℕ, ∀ a d,
    ⟨a, 0, 0, d+1, k⟩ [fm]⊢* ⟨a+2*k, 0, 0, d+1+3*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show d + 1 = d + 1 from rfl]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 2: R5+R3+R1+R1 rounds, each round a-=1, c-=2, e+=1
theorem phase2_loop : ∀ k : ℕ, ∀ a c e,
    ⟨a+k, 0, c+2*k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Even transition: d = 2k+2, a = m+k+2
theorem trans_even : ∀ k : ℕ, ∀ m,
    ⟨m+k+2, 0, 0, 2*k+2, 0⟩ [fm]⊢⁺ ⟨m+2*k+6, 0, 0, 3*k+10, 0⟩ := by
  intro k m
  -- Phase 1: d→c (⊢*)
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_c (2*k+2) (m+k+2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: (k+1) rounds (⊢*)
  apply stepStar_stepPlus_stepPlus
  · have h := phase2_loop (k+1) (m+1) 0 0
    simp only [Nat.zero_add] at h
    rw [show m + 1 + (k + 1) = m + k + 2 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring] at h
    exact h
  -- R5 step (⊢⁺)
  apply step_stepStar_stepPlus
  · show fm ⟨(m) + 1, 0, 0, 0, k + 1⟩ = some ⟨m, 0, 0, 0 + 1, (k + 1) + 2⟩
    simp [fm]
  -- Inner loop (⊢*)
  apply stepStar_trans
  · have h := inner_loop (k+3) m 0
    simp only [Nat.zero_add] at h; exact h
  ring_nf; finish

-- Odd transition: d = 2k+1, a = m+k+1
theorem trans_odd : ∀ k : ℕ, ∀ m,
    ⟨m+k+1, 0, 0, 2*k+1, 0⟩ [fm]⊢⁺ ⟨m+2*k+3, 0, 0, 3*k+5, 0⟩ := by
  intro k m
  -- Phase 1: d→c (⊢*)
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_c (2*k+1) (m+k+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: k rounds (⊢*)
  apply stepStar_stepPlus_stepPlus
  · have h := phase2_loop k (m+1) 1 0
    rw [show m + 1 + k = m + k + 1 from by ring,
        show 1 + 2 * k = 2 * k + 1 from by ring,
        show 0 + k = k from by ring] at h
    exact h
  -- R5: (m+1, 0, 1, 0, k) → (m, 0, 1, 1, k+2)
  apply step_stepStar_stepPlus
  · show fm ⟨(m) + 1, 0, 1, 0, k⟩ = some ⟨m, 0, 1, 0 + 1, k + 2⟩
    simp [fm]
  -- R3: (m, 0, 1, 1, k+2) → (m, 2, 1, 0, k+1)
  apply stepStar_trans
  · have : ⟨m, 0, 1, 1, k+2⟩ [fm]⊢* ⟨m, 2, 1, 0, k+1⟩ := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, show k + 2 = (k+1) + 1 from by ring]
      step fm; finish
    exact this
  -- R1: (m, 2, 1, 0, k+1) → (m, 1, 0, 0, k+1)
  apply stepStar_trans
  · have : ⟨m, 2, 1, 0, k+1⟩ [fm]⊢* ⟨m, 1, 0, 0, k+1⟩ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
      step fm; finish
    exact this
  -- R2: (m, 1, 0, 0, k+1) → (m+1, 0, 0, 2, k+1)
  apply stepStar_trans
  · have : ⟨m, 1, 0, 0, k+1⟩ [fm]⊢* ⟨m+1, 0, 0, 2, k+1⟩ := by
      rw [show (1 : ℕ) = 0 + 1 from rfl]
      step fm; finish
    exact this
  -- Inner loop: (m+1, 0, 0, 2, k+1) →* target
  apply stepStar_trans
  · have h := inner_loop (k+1) (m+1) 1
    rw [show 1 + 1 = 2 from rfl] at h; exact h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 7, 0⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ 2 * a > d)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    rcases Nat.even_or_odd d with ⟨n, hn⟩ | ⟨n, hn⟩
    · -- Even: d = n + n, n ≥ 1
      have hn1 : n ≥ 1 := by omega
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [show (k + 1) + (k + 1) = 2 * k + 2 from by ring] at hn
      subst hn
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
      refine ⟨⟨m + 2*k + 6, 0, 0, 3*k + 10, 0⟩,
              ⟨m + 2*k + 6, 3*k + 10, rfl, ?_, ?_⟩, ?_⟩
      · omega
      · omega
      · exact trans_even k m
    · -- Odd: d = 2n + 1
      rw [show 2 * n + 1 = 2 * n + 1 from rfl] at hn
      subst hn
      obtain ⟨m, rfl⟩ : ∃ m, a = m + n + 1 := ⟨a - n - 1, by omega⟩
      refine ⟨⟨m + 2*n + 3, 0, 0, 3*n + 5, 0⟩,
              ⟨m + 2*n + 3, 3*n + 5, rfl, ?_, ?_⟩, ?_⟩
      · omega
      · omega
      · exact trans_odd n m
  · exact ⟨4, 7, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_63
