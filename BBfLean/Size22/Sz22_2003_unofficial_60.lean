import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #60: [1/15, 98/3, 27/77, 5/7, 99/2]

Vector representation:
```
 0 -1 -1  0  0
 1 -1  0  2  0
 0  3  0 -1 -1
 0  0  1 -1  0
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_60

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- R4 chain: transfers d to c (b=0, e=0 so R4 fires)
theorem r4_chain : ∀ k, ∀ a c d, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a (c + 1) d)
  ring_nf; finish

-- R5/R1/R1 chain: each round consumes 1 from a, 2 from c, adds 1 to e
theorem r5r1r1_chain : ∀ k, ∀ a c e,
    ⟨a + k, 0, c + 2 * k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih a c (e + 1))
  ring_nf; finish

-- R3/R2/R2/R2 chain: each round adds 3 to a, 5 to d, subtracts 1 from e
theorem r3r2r2r2_chain : ∀ k, ∀ a d,
    ⟨a, 0, 0, d + 1, k⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, d + 5 * k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  step fm; step fm; step fm; step fm
  apply stepStar_trans (ih (a + 3) (d + 5))
  ring_nf; finish

-- Odd transition: d = 2k+1, a >= k+1
-- (a, 0, 0, 2k+1, 0) ->+ (a+2k+3, 0, 0, 5k+7, 0)
theorem transition_odd (n k : ℕ) :
    ⟨n + k + 1, 0, 0, 2 * k + 1, 0⟩ [fm]⊢⁺ ⟨n + 3 * k + 4, 0, 0, 5 * k + 7, 0⟩ := by
  -- Phase 1: R4 (2k+1) times -> (n+k+1, 0, 2k+1, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + k + 1, 0, 2 * k + 1, 0, 0⟩)
  · have h := r4_chain (2 * k + 1) (n + k + 1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: k rounds of R5/R1/R1 -> (n+1, 0, 1, 0, k)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + 1, 0, 1, 0, k⟩)
  · have h := r5r1r1_chain k (n + 1) 1 0
    simp only [Nat.zero_add] at h
    rw [show n + 1 + k = n + k + 1 from by ring,
        show 1 + 2 * k = 2 * k + 1 from by ring] at h; exact h
  -- Partial round: R5 -> R1 -> R2 -> (n+1, 0, 0, 2, k+1)
  apply step_stepStar_stepPlus
  · show fm ⟨n + 1, 0, 1, 0, k⟩ = some ⟨n, 2, 1, 0, k + 1⟩; simp [fm]
  step fm; step fm
  -- Phase 3: R3/R2/R2/R2 chain (k+1) rounds
  have h := r3r2r2r2_chain (k + 1) (n + 1) 1
  rw [show 1 + 1 = 2 from by ring] at h
  apply stepStar_trans h
  ring_nf; finish

-- Even transition: d = 2k, k >= 1, a >= k+1
-- (a, 0, 0, 2k, 0) ->+ (a+2k+4, 0, 0, 5k+9, 0)
theorem transition_even (n k : ℕ) (_ : k ≥ 1) :
    ⟨n + k + 1, 0, 0, 2 * k, 0⟩ [fm]⊢⁺ ⟨n + 3 * k + 5, 0, 0, 5 * k + 9, 0⟩ := by
  -- Phase 1: R4 (2k) times -> (n+k+1, 0, 2k, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + k + 1, 0, 2 * k, 0, 0⟩)
  · have h := r4_chain (2 * k) (n + k + 1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: k rounds of R5/R1/R1 -> (n+1, 0, 0, 0, k)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + 1, 0, 0, 0, k⟩)
  · have h := r5r1r1_chain k (n + 1) 0 0
    simp only [Nat.zero_add] at h
    rw [show n + 1 + k = n + k + 1 from by ring] at h; exact h
  -- R5 -> R2 -> R2 -> (n+2, 0, 0, 4, k+1)
  apply step_stepStar_stepPlus
  · show fm ⟨n + 1, 0, 0, 0, k⟩ = some ⟨n, 2, 0, 0, k + 1⟩; simp [fm]
  step fm; step fm
  -- Phase 3: R3/R2/R2/R2 chain (k+1) rounds
  have h := r3r2r2r2_chain (k + 1) (n + 2) 3
  rw [show 3 + 1 = 4 from by ring] at h
  apply stepStar_trans h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 9, 0⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ 2 * a ≥ d + 1 ∧ d ≥ 1)
  · intro c ⟨a, d, hq, ha, hd⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d = 2K (even), K >= 1 since d >= 1
      have hK1 : K ≥ 1 := by omega
      have ha2 : a ≥ K + 1 := by omega
      set n := a - K - 1 with hn_def
      have ha_eq : a = n + K + 1 := by omega
      have hd_eq : d = 2 * K := by omega
      rw [ha_eq, hd_eq]
      exact ⟨_, ⟨n + 3 * K + 5, 5 * K + 9, rfl, by omega, by omega⟩,
        transition_even n K hK1⟩
    · -- d = 2K + 1 (odd)
      -- a >= K+1 since 2a >= d+1 = 2K+2
      have ha2 : a ≥ K + 1 := by omega
      set n := a - K - 1 with hn_def
      have ha_eq : a = n + K + 1 := by omega
      rw [ha_eq, hK]
      exact ⟨_, ⟨n + 3 * K + 4, 5 * K + 7, rfl, by omega, by omega⟩,
        transition_odd n K⟩
  · exact ⟨5, 9, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_60
