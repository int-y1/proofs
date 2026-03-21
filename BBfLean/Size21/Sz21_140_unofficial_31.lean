import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #31: [35/6, 121/2, 4/55, 3/7, 15/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_31

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 repeated: d → b
theorem d_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- One R1,R1,R3 round: 3 steps
-- (2, B+2, C, D, E+1) → R1 → (1, B+1, C+1, D+1, E+1) → R1 → (0, B, C+2, D+2, E+1) → R3 → (2, B, C+1, D+2, E)
theorem r1r1r3_one : ⟨2, B+2, C, D, E+1⟩ [fm]⊢⁺ ⟨2, B, C+1, D+2, E⟩ := by
  rw [show B + 2 = (B + 1) + 1 from by ring]
  step fm
  -- Goal: (1, B + 1, C + 1, D + 1, E + 1) ⊢* (2, B, C + 1, D + 2, E)
  -- Need to fire R1 again: (0+1, B+1, C+1, D+1, E+1) matches R1 with a+1, b+1
  -- After: (0, B, C+2, D+2, E+1)
  -- Then R3: (0, B, (C+1)+1, D+2, E+1) matches c+1, but e+1 needs E+1 to be (E)+1
  -- → (2, B, C+1, D+2, E)
  step fm
  -- Goal: (0, B, C + 2, D + 2, E + 1) ⊢* (2, B, C + 1, D + 2, E)
  -- C + 2 = (C+1) + 1, E + 1 = E + 1: R3 matches
  step fm
  finish

-- R1,R1,R3 chain by induction
theorem r1r1r3_rounds : ∀ k, ∀ C D, ⟨2, B+2*k, C, D, E+k⟩ [fm]⊢* ⟨2, B, C+k, D+2*k, E⟩ := by
  intro k; induction' k with k h <;> intro C D
  · exists 0
  have h1 : ⟨2, B+2*k+2, C, D, E+k+1⟩ [fm]⊢⁺ ⟨2, B+2*k, C+1, D+2, E+k⟩ := by
    have := @r1r1r3_one (B + 2 * k) C D (E + k)
    rw [show B + 2 * k + 2 = B + 2 * k + 2 from rfl,
        show E + k + 1 = E + k + 1 from rfl] at this
    exact this
  rw [show B + 2 * (k + 1) = B + 2 * k + 2 from by ring,
      show E + (k + 1) = E + k + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar h1)
  have h2 := h (C + 1) (D + 2)
  rw [show D + 2 + 2 * k = D + 2 * (k + 1) from by ring] at h2
  refine stepStar_trans h2 ?_; ring_nf; finish

-- One R2,R2,R3 round: 3 steps
-- (2, 0, C+1, D, E) → R2 → (1, 0, C+1, D, E+2) → R2 → (0, 0, C+1, D, E+4) → R3 → (2, 0, C, D, E+3)
theorem r2r2r3_one : ⟨2, 0, C+1, D, E⟩ [fm]⊢⁺ ⟨2, 0, C, D, E+3⟩ := by
  step fm
  -- Goal: (1, 0, C + 1, D, E + 2) ⊢* (2, 0, C, D, E + 3)
  -- R2: (0+1, 0, C+1, D, E+2) → (0, 0, C+1, D, E+4)
  step fm
  -- Goal: (0, 0, C + 1, D, E + 4) ⊢* (2, 0, C, D, E + 3)
  -- R3: (0, 0, (C)+1, D, (E+3)+1) → (2, 0, C, D, E+3)
  rw [show E + 4 = (E + 3) + 1 from by ring]
  step fm
  finish

-- R2,R2,R3 chain by induction
theorem r2r2r3_rounds : ∀ k, ∀ C E, ⟨2, 0, C+k, D, E⟩ [fm]⊢* ⟨2, 0, C, D, E+3*k⟩ := by
  intro k; induction' k with k h <;> intro C E
  · exists 0
  have h1 : ⟨2, 0, C+k+1, D, E⟩ [fm]⊢⁺ ⟨2, 0, C+k, D, E+3⟩ := by
    rw [show C + k + 1 = (C + k) + 1 from by ring]
    exact r2r2r3_one
  rw [show C + (k + 1) = C + k + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar h1)
  have h2 := h C (E + 3)
  refine stepStar_trans h2 ?_; ring_nf; finish

-- Phase 4 even: d+1 = 2K, E ≥ K
theorem phase4_even (K : ℕ) (hEK : E ≥ K) : ⟨2, 2*K, 0, 0, E⟩ [fm]⊢* ⟨0, 0, 0, 2*K, E+2*K+4⟩ := by
  -- Write E = E' + K
  obtain ⟨E', rfl⟩ : ∃ E', E = E' + K := ⟨E - K, by omega⟩
  -- R1R1R3 K rounds
  apply stepStar_trans (c₂ := ⟨2, 0, K, 2*K, E'⟩)
  · have h := @r1r1r3_rounds 0 E' K 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R2R2R3 K rounds
  apply stepStar_trans (c₂ := ⟨2, 0, 0, 2*K, E'+3*K⟩)
  · have h := @r2r2r3_rounds (2*K) K 0 E'
    simp only [Nat.zero_add] at h; exact h
  -- Final R2,R2: 2 steps
  step fm; step fm
  rw [show E' + 3 * K + 2 + 2 = E' + K + (2 * K + 4) from by ring]; finish

-- Phase 4 odd: d+1 = 2K+1, E ≥ K
theorem phase4_odd (K : ℕ) (hEK : E ≥ K) : ⟨2, 2*K+1, 0, 0, E⟩ [fm]⊢* ⟨0, 0, 0, 2*K+1, E+2*K+5⟩ := by
  -- Write E = E' + K
  obtain ⟨E', rfl⟩ : ∃ E', E = E' + K := ⟨E - K, by omega⟩
  -- R1R1R3 K rounds: (2, 1+2*K, 0, 0, E'+K) →* (2, 1, K, 2*K, E')
  apply stepStar_trans (c₂ := ⟨2, 1, K, 2*K, E'⟩)
  · rw [show 2 * K + 1 = 1 + 2 * K from by ring]
    have h := @r1r1r3_rounds 1 E' K 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R1: (1+1, 0+1, K, 2*K, E') → (1, 0, K+1, 2*K+1, E')
  apply stepStar_trans (c₂ := ⟨1, 0, K+1, 2*K+1, E'⟩)
  · rw [show (2 : ℕ) = 1 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
    step fm; finish
  -- R2: (0+1, 0, K+1, 2*K+1, E') → (0, 0, K+1, 2*K+1, E'+2)
  apply stepStar_trans (c₂ := ⟨0, 0, K+1, 2*K+1, E'+2⟩)
  · rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm; finish
  -- R3: (0, 0, (K)+1, 2*K+1, (E'+1)+1) → (2, 0, K, 2*K+1, E'+1)
  apply stepStar_trans (c₂ := ⟨2, 0, K, 2*K+1, E'+1⟩)
  · rw [show E' + 2 = (E' + 1) + 1 from by ring]
    step fm; finish
  -- R2R2R3 K rounds
  apply stepStar_trans (c₂ := ⟨2, 0, 0, 2*K+1, E'+1+3*K⟩)
  · have h := @r2r2r3_rounds (2*K+1) K 0 (E'+1)
    simp only [Nat.zero_add] at h; exact h
  -- Final R2,R2: 2 steps
  step fm; step fm
  rw [show E' + 1 + 3 * K + 2 + 2 = E' + K + (2 * K + 5) from by ring]; finish

-- Main transition
theorem main_trans (hde : e ≥ d + 2) : ⟨0, 0, 0, d, e⟩ [fm]⊢⁺ ⟨0, 0, 0, d+1, e+d+3⟩ := by
  -- Phase 1: (0, 0, 0, d, e) →* (0, d, 0, 0, e)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, d, 0, 0, e⟩)
  · have h := @d_to_b e d 0 0; simp only [Nat.zero_add] at h; exact h
  -- Write e = E + 2
  obtain ⟨E, rfl⟩ : ∃ E, e = E + 2 := ⟨e - 2, by omega⟩
  -- R5: (0, d, 0, 0, (E+1)+1) → (0, d+1, 1, 0, E+1)
  apply step_stepStar_stepPlus
  · show fm ⟨0, d, 0, 0, (E + 1) + 1⟩ = some ⟨0, d + 1, 1, 0, E + 1⟩; simp [fm]
  -- R3: (0, d+1, (0)+1, 0, (E)+1) → (2, d+1, 0, 0, E)
  apply stepStar_trans (c₂ := ⟨2, d+1, 0, 0, E⟩)
  · step fm; finish
  -- Phase 4: parity split on d+1
  rcases Nat.even_or_odd (d + 1) with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- d+1 = K+K = 2K
    rw [show K + K = 2 * K from by ring] at hK
    have hEK : E ≥ K := by omega
    rw [hK]
    rw [show E + 2 + d + 3 = E + 2 * K + 4 from by omega]
    exact phase4_even K hEK
  · -- d+1 = 2K+1
    have hd2K : d = 2 * K := by omega
    have hEK : E ≥ K := by omega
    rw [show d + 1 = 2 * K + 1 from by omega]
    -- Goal: (2, 2*K+1, 0, 0, E) ⊢* (0, 0, 0, 2*K+1, E+2+d+3)
    rw [show E + 2 + d + 3 = E + 2 * K + 5 from by omega]
    exact phase4_odd K hEK

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ e ≥ d + 2)
  · intro c ⟨d, e, hc, hde⟩
    refine ⟨⟨0, 0, 0, d+1, e+d+3⟩, ⟨d+1, e+d+3, rfl, by omega⟩, ?_⟩
    rw [hc]; exact main_trans hde
  · exact ⟨0, 2, rfl, by omega⟩

end Sz21_140_unofficial_31
