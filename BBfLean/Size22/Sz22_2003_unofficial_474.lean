import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #474: [28/15, 27/49, 1/6, 25/2, 3/5]

Vector representation:
```
 2 -1 -1  1
 0  3  0 -2
-1 -1  0  0
-1  0  2  0
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_474

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+1⟩
  | ⟨a, b, c, d+2⟩ => some ⟨a, b+3, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4 chain with d=0: convert a to c
theorem r4_chain : ∀ k a c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3 drain: simultaneously remove from a and b
theorem r3_drain : ∀ k a, ⟨a+k, k, 0, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R2 drain: convert even d to b
theorem r2_drain : ∀ k a b, ⟨a, b, 0, 2*k⟩ [fm]⊢* ⟨a, b+3*k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Bootstrap: (0, 0, c+2, 0) → (2, 3, c+2, 0) in 7 steps
theorem bootstrap (c : ℕ) : ⟨0, 0, c+2, 0⟩ [fm]⊢* ⟨2, 3, c+2, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- One R1R1R1R2 round: (a, 3, c+3, d) → (a+6, 3, c, d+1)
theorem r1r1r1r2 (c d a : ℕ) : ⟨a, 3, c+3, d⟩ [fm]⊢* ⟨a+6, 3, c, d+1⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Chain of k R1R1R1R2 rounds
theorem r1r1r1r2_chain : ∀ k c d a, ⟨a, 3, c+3*k, d⟩ [fm]⊢* ⟨a+6*k, 3, c, d+k⟩ := by
  intro k; induction' k with k h <;> intro c d a
  · exists 0
  rw [show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring]
  apply stepStar_trans (r1r1r1r2 _ _ _)
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition for n ≡ 0 mod 3: n = 3j, canonical (0, 0, 6j+2, 0)
theorem main_trans_mod0 (j : ℕ) : ⟨0, 0, 6*j+2, 0⟩ [fm]⊢⁺ ⟨0, 0, 18*j+4, 0⟩ := by
  -- First R5 step for ⊢⁺
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 6 * j + 2, 0⟩ = some ⟨0, 1, 6 * j + 1, 0⟩
    simp [fm]
  -- Remaining 6 bootstrap steps
  step fm; step fm; step fm; step fm; step fm; step fm
  -- Now at (2, 3, 6j+2, 0). Chain: 2j rounds → (12j+2, 3, 2, 2j)
  apply stepStar_trans
  · have h := r1r1r1r2_chain (2*j) 2 0 2
    simp only [(by ring : 2 + 3 * (2 * j) = 6 * j + 2),
               (by ring : 2 + 6 * (2 * j) = 12 * j + 2),
               (by ring : 0 + 2 * j = 2 * j)] at h
    exact h
  -- Cleanup r=2: two R1 steps
  step fm; step fm
  -- Now at (12j+6, 1, 0, 2j+2). R2 drain.
  apply stepStar_trans
  · have h := r2_drain (j+1) (12*j+6) 1
    simp only [(by ring : 2 * (j + 1) = 2 * j + 2),
               (by ring : 1 + 3 * (j + 1) = 3 * j + 4)] at h
    exact h
  -- R3 drain: (12j+6, 3j+4, 0, 0) → (9j+2, 0, 0, 0)
  apply stepStar_trans
  · have h := r3_drain (3*j+4) (9*j+2)
    simp only [(by ring : 9 * j + 2 + (3 * j + 4) = 12 * j + 6)] at h
    exact h
  -- R4 chain: (9j+2, 0, 0, 0) → (0, 0, 18j+4, 0)
  have h := r4_chain (9*j+2) 0 0
  simp only [Nat.zero_add, (by ring : 2 * (9 * j + 2) = 18 * j + 4)] at h
  exact h

-- Main transition for n ≡ 1 mod 3: n = 3j+1
theorem main_trans_mod1 (j : ℕ) : ⟨0, 0, 6*j+4, 0⟩ [fm]⊢⁺ ⟨0, 0, 18*j+10, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 6 * j + 4, 0⟩ = some ⟨0, 1, 6 * j + 3, 0⟩
    simp [fm]
  step fm; step fm; step fm; step fm; step fm; step fm
  -- Now at (2, 3, 6j+4, 0). Chain: 2j+1 rounds → (12j+8, 3, 1, 2j+1)
  apply stepStar_trans
  · have h := r1r1r1r2_chain (2*j+1) 1 0 2
    simp only [(by ring : 1 + 3 * (2 * j + 1) = 6 * j + 4),
               (by ring : 2 + 6 * (2 * j + 1) = 12 * j + 8),
               (by ring : 0 + (2 * j + 1) = 2 * j + 1)] at h
    exact h
  -- Cleanup r=1: one R1 step
  step fm
  -- Now at (12j+10, 2, 0, 2j+2). R2 drain.
  apply stepStar_trans
  · have h := r2_drain (j+1) (12*j+10) 2
    simp only [(by ring : 2 * (j + 1) = 2 * j + 2),
               (by ring : 2 + 3 * (j + 1) = 3 * j + 5)] at h
    exact h
  -- R3 drain
  apply stepStar_trans
  · have h := r3_drain (3*j+5) (9*j+5)
    simp only [(by ring : 9 * j + 5 + (3 * j + 5) = 12 * j + 10)] at h
    exact h
  -- R4 chain
  have h := r4_chain (9*j+5) 0 0
  simp only [Nat.zero_add, (by ring : 2 * (9 * j + 5) = 18 * j + 10)] at h
  exact h

-- Main transition for n ≡ 2 mod 3: n = 3j+2
theorem main_trans_mod2 (j : ℕ) : ⟨0, 0, 6*j+6, 0⟩ [fm]⊢⁺ ⟨0, 0, 18*j+16, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 6 * j + 6, 0⟩ = some ⟨0, 1, 6 * j + 5, 0⟩
    simp [fm]
  step fm; step fm; step fm; step fm; step fm; step fm
  -- Now at (2, 3, 6j+6, 0). Chain: 2j+2 rounds → (12j+14, 3, 0, 2j+2)
  apply stepStar_trans
  · have h := r1r1r1r2_chain (2*j+2) 0 0 2
    simp only [(by ring : 0 + 3 * (2 * j + 2) = 6 * j + 6),
               (by ring : 2 + 6 * (2 * j + 2) = 12 * j + 14),
               (by ring : 0 + (2 * j + 2) = 2 * j + 2)] at h
    exact h
  -- Cleanup r=0: R2 drain directly
  apply stepStar_trans
  · have h := r2_drain (j+1) (12*j+14) 3
    simp only [(by ring : 2 * (j + 1) = 2 * j + 2),
               (by ring : 3 + 3 * (j + 1) = 3 * j + 6)] at h
    exact h
  -- R3 drain
  apply stepStar_trans
  · have h := r3_drain (3*j+6) (9*j+8)
    simp only [(by ring : 9 * j + 8 + (3 * j + 6) = 12 * j + 14)] at h
    exact h
  -- R4 chain
  have h := r4_chain (9*j+8) 0 0
  simp only [Nat.zero_add, (by ring : 2 * (9 * j + 8) = 18 * j + 16)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, 2*n+2, 0⟩)
  · intro q ⟨n, hn⟩
    subst hn
    have hmod : n % 3 < 3 := Nat.mod_lt _ (by omega)
    have hdiv : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
    interval_cases (n % 3)
    · -- n ≡ 0 mod 3: n = 3j
      obtain ⟨j, rfl⟩ := Nat.dvd_of_mod_eq_zero (by omega : n % 3 = 0)
      clear hdiv hmod
      refine ⟨⟨0, 0, 18*j+4, 0⟩, ⟨9*j+1, ?_⟩, ?_⟩
      · ring_nf
      · convert main_trans_mod0 j using 2; ring_nf
    · -- n ≡ 1 mod 3: n = 3j+1
      have ⟨j, hj⟩ : ∃ j, n = 3 * j + 1 := ⟨n / 3, by omega⟩
      subst hj; clear hdiv hmod
      refine ⟨⟨0, 0, 18*j+10, 0⟩, ⟨9*j+4, ?_⟩, ?_⟩
      · ring_nf
      · convert main_trans_mod1 j using 2; ring_nf
    · -- n ≡ 2 mod 3: n = 3j+2
      have ⟨j, hj⟩ : ∃ j, n = 3 * j + 2 := ⟨n / 3, by omega⟩
      subst hj; clear hdiv hmod
      refine ⟨⟨0, 0, 18*j+16, 0⟩, ⟨9*j+7, ?_⟩, ?_⟩
      · ring_nf
      · convert main_trans_mod2 j using 2; ring_nf
  · exact ⟨0, by simp⟩

end Sz22_2003_unofficial_474
