import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #37: [35/6, 143/2, 4/55, 3/7, 6/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_37

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e, f⟩
  | _ => none

-- Phase: R4 repeated, d → b (when a=0, c=0)
theorem d_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase: R1R1R3 triple round
-- Each round: (2, B+2, C, D, E+1, F) → (2, B, C+1, D+2, E, F) in 3 steps
-- k rounds: (2, B+2k, C, D, E+k, F) →* (2, B, C+k, D+2k, E, F)
theorem r1r1r3_rounds : ∀ k, ∀ C D E, ⟨2, B+2*k, C, D, E+k, F⟩ [fm]⊢* ⟨(2 : ℕ), B, C+k, D+2*k, E, F⟩ := by
  intro k; induction' k with k ih <;> intro C D E
  · exists 0
  rw [show B + 2 * (k + 1) = (B + 2 * k) + 1 + 1 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (C + 1) (D + 2) E)
  ring_nf; finish

-- Phase: R2R2R3 chain: consume c, building e and f
-- k rounds: (2, 0, C+k, D, E, F) →* (2, 0, C, D, E+k, F+2*k)
theorem r2r2r3_chain : ∀ k, ∀ C E F, ⟨2, 0, C+k, D, E, F⟩ [fm]⊢* ⟨(2 : ℕ), 0, C, D, E+k, F+2*k⟩ := by
  intro k; induction' k with k ih <;> intro C E F
  · exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring]
  step fm; step fm
  rw [show E + 2 = (E + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (ih C (E + 1) (F + 2))
  ring_nf; finish

-- Main transition for odd n: n = 2*K+1
-- Canonical: (2, 0, 0, 2K+2, 2K+1, F) ⊢⁺ (2, 0, 0, 2K+3, 2K+2, F+2K+3)
theorem main_trans_odd (K : ℕ) (F : ℕ) : ⟨2, 0, 0, 2*K+2, 2*K+1, F⟩ [fm]⊢⁺ ⟨(2 : ℕ), 0, 0, 2*K+3, 2*K+2, F+2*K+3⟩ := by
  -- Phase 1: 2 R2 steps → (0, 0, 0, 2K+2, 2K+3, F+2)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, 0, 2*K+2, 2*K+2, F+1⟩)
  · show fm ⟨1+1, 0, 0, 2*K+2, 2*K+1, F⟩ = some ⟨1, 0, 0, 2*K+2, 2*K+2, F+1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 2*K+2, 2*K+3, F+2⟩)
  · have : ⟨1, 0, 0, 2*K+2, 2*K+2, F+1⟩ [fm]⊢ ⟨(0 : ℕ), 0, 0, 2*K+2, 2*K+3, F+2⟩ := by
      show fm ⟨0+1, 0, 0, 2*K+2, 2*K+2, F+1⟩ = some ⟨0, 0, 0, 2*K+2, 2*K+3, F+2⟩; simp [fm]
    exact step_stepStar this
  -- Phase 2: R4 chain (2K+2 steps) → (0, 2K+2, 0, 0, 2K+3, F+2)
  apply stepStar_trans (c₂ := ⟨0, 2*K+2, 0, 0, 2*K+3, F+2⟩)
  · have h := @d_to_b (2*K+3) (F+2) (2*K+2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 step → (1, 2K+3, 0, 0, 2K+3, F+1)
  apply stepStar_trans (c₂ := ⟨1, 2*K+3, 0, 0, 2*K+3, F+1⟩)
  · rw [show F + 2 = F + 1 + 1 from by ring]
    have : ⟨0, 2*K+2, 0, 0, 2*K+3, F+1+1⟩ [fm]⊢ ⟨(1 : ℕ), 2*K+3, 0, 0, 2*K+3, F+1⟩ := by
      show fm ⟨0, 2*K+2, 0, 0, 2*K+3, (F+1)+1⟩ = some ⟨0+1, (2*K+2)+1, 0, 0, 2*K+3, F+1⟩
      simp [fm]
    exact step_stepStar this
  -- Phase 4: R1, R3 → (2, 2K+2, 0, 1, 2K+2, F+1)
  apply stepStar_trans (c₂ := ⟨2, 2*K+2, 0, 1, 2*K+2, F+1⟩)
  · have h1 : ⟨1, 2*K+3, 0, 0, 2*K+3, F+1⟩ [fm]⊢ ⟨(0 : ℕ), 2*K+2, 1, 1, 2*K+3, F+1⟩ := by
      rw [show 2 * K + 3 = (2 * K + 2) + 1 from by ring]
      show fm ⟨0+1, (2*K+2)+1, 0, 0, 2*K+3, F+1⟩ = some ⟨0, 2*K+2, 1, 1, 2*K+3, F+1⟩
      simp [fm]
    have h2 : ⟨(0 : ℕ), 2*K+2, 1, 1, 2*K+3, F+1⟩ [fm]⊢ ⟨(2 : ℕ), 2*K+2, 0, 1, 2*K+2, F+1⟩ := by
      rw [show 2 * K + 3 = (2 * K + 2) + 1 from by ring]
      show fm ⟨0, 2*K+2, 0+1, 1, (2*K+2)+1, F+1⟩ = some ⟨0+2, 2*K+2, 0, 1, 2*K+2, F+1⟩
      simp [fm]
    exact stepStar_trans (step_stepStar h1) (step_stepStar h2)
  -- Phase 5: K+1 R1R1R3 rounds → (2, 0, K+1, 2K+3, K+1, F+1)
  apply stepStar_trans (c₂ := ⟨2, 0, K+1, 2*K+3, K+1, F+1⟩)
  · have h := @r1r1r3_rounds 0 (F+1) (K+1) 0 1 (K+1)
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  -- Phase 6: R2, R2, R3 start → (2, 0, K, 2K+3, K+2, F+3)
  apply stepStar_trans (c₂ := ⟨2, 0, K, 2*K+3, K+2, F+3⟩)
  · -- R2: (2, 0, K+1, 2K+3, K+1, F+1) → (1, 0, K+1, 2K+3, K+2, F+2)
    -- R2: (1, 0, K+1, 2K+3, K+2, F+2) → (0, 0, K+1, 2K+3, K+3, F+3)
    -- R3: (0, 0, K+1, 2K+3, K+3, F+3) → (2, 0, K, 2K+3, K+2, F+3)
    have h1 : ⟨2, 0, K+1, 2*K+3, K+1, F+1⟩ [fm]⊢ ⟨(1 : ℕ), 0, K+1, 2*K+3, K+2, F+2⟩ := by
      show fm ⟨1+1, 0, K+1, 2*K+3, K+1, F+1⟩ = some ⟨1, 0, K+1, 2*K+3, K+2, F+2⟩; simp [fm]
    have h2 : ⟨1, 0, K+1, 2*K+3, K+2, F+2⟩ [fm]⊢ ⟨(0 : ℕ), 0, K+1, 2*K+3, K+3, F+3⟩ := by
      show fm ⟨0+1, 0, K+1, 2*K+3, K+2, F+2⟩ = some ⟨0, 0, K+1, 2*K+3, K+3, F+3⟩; simp [fm]
    have h3 : ⟨(0 : ℕ), 0, K+1, 2*K+3, K+3, F+3⟩ [fm]⊢ ⟨(2 : ℕ), 0, K, 2*K+3, K+2, F+3⟩ := by
      rw [show K + 1 = K + 1 from rfl, show K + 3 = (K + 2) + 1 from by ring]
      show fm ⟨0, 0, K+1, 2*K+3, (K+2)+1, F+3⟩ = some ⟨0+2, 0, K, 2*K+3, K+2, F+3⟩
      simp [fm]
    exact stepStar_trans (step_stepStar h1) (stepStar_trans (step_stepStar h2) (step_stepStar h3))
  -- Phase 7: K R2R2R3 rounds → (2, 0, 0, 2K+3, 2K+2, F+3+2K)
  have h := @r2r2r3_chain (2*K+3) K 0 (K+2) (F+3)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Main transition for even n: n = 2*K
-- Canonical: (2, 0, 0, 2K+1, 2K, F) ⊢⁺ (2, 0, 0, 2K+2, 2K+1, F+2K+2)
theorem main_trans_even (K : ℕ) (F : ℕ) : ⟨2, 0, 0, 2*K+1, 2*K, F⟩ [fm]⊢⁺ ⟨(2 : ℕ), 0, 0, 2*K+2, 2*K+1, F+2*K+2⟩ := by
  -- Phase 1: 2 R2 steps → (0, 0, 0, 2K+1, 2K+2, F+2)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, 0, 2*K+1, 2*K+1, F+1⟩)
  · show fm ⟨1+1, 0, 0, 2*K+1, 2*K, F⟩ = some ⟨1, 0, 0, 2*K+1, 2*K+1, F+1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 2*K+1, 2*K+2, F+2⟩)
  · have : ⟨1, 0, 0, 2*K+1, 2*K+1, F+1⟩ [fm]⊢ ⟨(0 : ℕ), 0, 0, 2*K+1, 2*K+2, F+2⟩ := by
      show fm ⟨0+1, 0, 0, 2*K+1, 2*K+1, F+1⟩ = some ⟨0, 0, 0, 2*K+1, 2*K+2, F+2⟩; simp [fm]
    exact step_stepStar this
  -- Phase 2: R4 chain (2K+1 steps) → (0, 2K+1, 0, 0, 2K+2, F+2)
  apply stepStar_trans (c₂ := ⟨0, 2*K+1, 0, 0, 2*K+2, F+2⟩)
  · have h := @d_to_b (2*K+2) (F+2) (2*K+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 step → (1, 2K+2, 0, 0, 2K+2, F+1)
  apply stepStar_trans (c₂ := ⟨1, 2*K+2, 0, 0, 2*K+2, F+1⟩)
  · rw [show F + 2 = F + 1 + 1 from by ring]
    have : ⟨0, 2*K+1, 0, 0, 2*K+2, F+1+1⟩ [fm]⊢ ⟨(1 : ℕ), 2*K+2, 0, 0, 2*K+2, F+1⟩ := by
      show fm ⟨0, 2*K+1, 0, 0, 2*K+2, (F+1)+1⟩ = some ⟨0+1, (2*K+1)+1, 0, 0, 2*K+2, F+1⟩
      simp [fm]
    exact step_stepStar this
  -- Phase 4: R1, R3 → (2, 2K+1, 0, 1, 2K+1, F+1)
  apply stepStar_trans (c₂ := ⟨2, 2*K+1, 0, 1, 2*K+1, F+1⟩)
  · have h1 : ⟨1, 2*K+2, 0, 0, 2*K+2, F+1⟩ [fm]⊢ ⟨(0 : ℕ), 2*K+1, 1, 1, 2*K+2, F+1⟩ := by
      rw [show 2 * K + 2 = (2 * K + 1) + 1 from by ring]
      show fm ⟨0+1, (2*K+1)+1, 0, 0, 2*K+2, F+1⟩ = some ⟨0, 2*K+1, 1, 1, 2*K+2, F+1⟩
      simp [fm]
    have h2 : ⟨(0 : ℕ), 2*K+1, 1, 1, 2*K+2, F+1⟩ [fm]⊢ ⟨(2 : ℕ), 2*K+1, 0, 1, 2*K+1, F+1⟩ := by
      rw [show 2 * K + 2 = (2 * K + 1) + 1 from by ring]
      show fm ⟨0, 2*K+1, 0+1, 1, (2*K+1)+1, F+1⟩ = some ⟨0+2, 2*K+1, 0, 1, 2*K+1, F+1⟩
      simp [fm]
    exact stepStar_trans (step_stepStar h1) (step_stepStar h2)
  -- Phase 5: K R1R1R3 rounds → (2, 1, K, 2K+1, K+1, F+1)
  apply stepStar_trans (c₂ := ⟨2, 1, K, 2*K+1, K+1, F+1⟩)
  · have h := @r1r1r3_rounds 1 (F+1) K 0 1 (K+1)
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  -- Phase 6: R1 → (1, 0, K+1, 2K+2, K+1, F+1)
  apply stepStar_trans (c₂ := ⟨1, 0, K+1, 2*K+2, K+1, F+1⟩)
  · have : ⟨2, 1, K, 2*K+1, K+1, F+1⟩ [fm]⊢ ⟨(1 : ℕ), 0, K+1, 2*K+2, K+1, F+1⟩ := by
      show fm ⟨1+1, 0+1, K, 2*K+1, K+1, F+1⟩ = some ⟨1, 0, K+1, 2*K+2, K+1, F+1⟩; simp [fm]
    exact step_stepStar this
  -- Phase 7: R2 → (0, 0, K+1, 2K+2, K+2, F+2)
  apply stepStar_trans (c₂ := ⟨0, 0, K+1, 2*K+2, K+2, F+2⟩)
  · have : ⟨1, 0, K+1, 2*K+2, K+1, F+1⟩ [fm]⊢ ⟨(0 : ℕ), 0, K+1, 2*K+2, K+2, F+2⟩ := by
      show fm ⟨0+1, 0, K+1, 2*K+2, K+1, F+1⟩ = some ⟨0, 0, K+1, 2*K+2, K+2, F+2⟩; simp [fm]
    exact step_stepStar this
  -- Phase 8: R3 → (2, 0, K, 2K+2, K+1, F+2)
  apply stepStar_trans (c₂ := ⟨2, 0, K, 2*K+2, K+1, F+2⟩)
  · have : ⟨(0 : ℕ), 0, K+1, 2*K+2, K+2, F+2⟩ [fm]⊢ ⟨(2 : ℕ), 0, K, 2*K+2, K+1, F+2⟩ := by
      rw [show K + 2 = (K + 1) + 1 from by ring]
      show fm ⟨0, 0, K+1, 2*K+2, (K+1)+1, F+2⟩ = some ⟨0+2, 0, K, 2*K+2, K+1, F+2⟩
      simp [fm]
    exact step_stepStar this
  -- Phase 9: K R2R2R3 rounds → (2, 0, 0, 2K+2, 2K+1, F+2+2K)
  have h := @r2r2r3_chain (2*K+2) K 0 (K+1) (F+2)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Combined main transition using parity split
theorem main_trans (d : ℕ) (f : ℕ) : ⟨2, 0, 0, d+1, d, f⟩ [fm]⊢⁺ ⟨(2 : ℕ), 0, 0, d+2, d+1, f+d+2⟩ := by
  rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- d = 2*K (even)
    rw [show K + K = 2 * K from by ring] at hK; subst hK
    exact main_trans_even K f
  · -- d = 2*K + 1 (odd)
    subst hK
    exact main_trans_odd K f

theorem nonhalt : ¬halts fm c₀ := by
  -- c₀ = (1, 0, 0, 0, 0, 0) reaches (2, 0, 0, 1, 0, 0) in 4 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, f⟩ ↦ ⟨2, 0, 0, d+1, d, f⟩) ⟨0, 0⟩
  intro ⟨d, f⟩; exact ⟨⟨d+1, f+d+2⟩, main_trans d f⟩

end Sz21_140_unofficial_37
