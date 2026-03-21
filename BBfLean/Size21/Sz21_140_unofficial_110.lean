import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #110: [7/45, 5/77, 242/5, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  0
 0  0  1 -1 -1
 1  0 -1  0  2
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_110

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 drain: e → b (when c=0, d=0)
theorem r4_drain : ∀ k, ∀ a b, ⟨a, b, 0, 0, k⟩ [fm]⊢* ⟨a, b+k, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3 drain (b=0): c → a,e (when d=0)
theorem r3_drain_b0 : ∀ k, ∀ a e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a+k, 0, 0, 0, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [show k + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3 drain (b=1): c → a,e (when d=0)
theorem r3_drain_b1 : ∀ k, ∀ a e, ⟨a, 1, k, 0, e⟩ [fm]⊢* ⟨a+k, 1, 0, 0, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [show k + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3R2R2 chain (b=0): one round (a, 0, c+1, d+2, 0) → (a+1, 0, c+2, d, 0)
-- Chain: ∀ k, ∀ a c d, (a, 0, c+1, d+2*k, 0) →* (a+k, 0, c+k+1, d, 0)
theorem r3r2r2_chain_b0 : ∀ k, ∀ a c d, ⟨a, 0, c+1, d+2*k, 0⟩ [fm]⊢* ⟨a+k, 0, c+k+1, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring,
      show c + 1 = c + 1 from rfl]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3R2R2 chain (b=1): same pattern
theorem r3r2r2_chain_b1 : ∀ k, ∀ a c d, ⟨a, 1, c+1, d+2*k, 0⟩ [fm]⊢* ⟨a+k, 1, c+k+1, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring,
      show c + 1 = c + 1 from rfl]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5+R1 chain: (a+k, b+2*k, 0, d, 0) →* (a, b, 0, d+2*k, 0)
theorem r5r1_chain : ∀ k, ∀ a b d, ⟨a+k, b+2*k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 1 (b=0 half): (a+1, 0, 0, 2*M+2, 0) →* (a+2*M+4, 0, 0, 0, 2*M+5)
theorem phase1_b0 : ⟨a+1, 0, 0, 2*M+2, 0⟩ [fm]⊢* ⟨a+2*M+4, 0, 0, 0, 2*M+5⟩ := by
  -- R5: (a+1, 0, 0, 2M+2, 0) → (a, 0, 1, 2M+3, 0)
  apply stepStar_trans (c₂ := ⟨a, 0, 1, 2*M+3, 0⟩)
  · rw [show a + 1 = a + 1 from rfl, show 2 * M + 2 = 2 * M + 2 from rfl]
    step fm; finish
  -- R3R2R2 chain: (a, 0, 1, 2M+3, 0) →* (a+M+1, 0, M+2, 1, 0)
  apply stepStar_trans (c₂ := ⟨a+M+1, 0, M+2, 1, 0⟩)
  · have h := @r3r2r2_chain_b0 (M+1) a 0 1
    rw [show 1 + 2 * (M + 1) = 2 * M + 3 from by ring,
        show 0 + 1 = 1 from by ring,
        show 0 + (M + 1) + 1 = M + 2 from by ring] at h
    exact h
  -- R3: (a+M+1, 0, M+2, 1, 0) → (a+M+2, 0, M+1, 1, 2)
  -- R2: → (a+M+2, 0, M+2, 0, 1)
  apply stepStar_trans (c₂ := ⟨a+M+2, 0, M+2, 0, 1⟩)
  · rw [show M + 2 = (M + 1) + 1 from by ring]
    step fm; step fm; ring_nf; finish
  -- R3 drain: (a+M+2, 0, M+2, 0, 1) →* (a+2M+4, 0, 0, 0, 2M+5)
  have h := @r3_drain_b0 (M+2) (a+M+2) 1
  rw [show a + M + 2 + (M + 2) = a + 2 * M + 4 from by ring,
      show 1 + 2 * (M + 2) = 2 * M + 5 from by ring] at h
  exact h

-- Phase 4 (b=1 half): (a+M+2, 1, 0, 2*M+4, 0) →* (a+3*M+7, 1, 0, 0, 2*M+7)
theorem phase4_b1 : ⟨a+M+2, 1, 0, 2*M+4, 0⟩ [fm]⊢* ⟨a+3*M+7, 1, 0, 0, 2*M+7⟩ := by
  -- R5: (a+M+2, 1, 0, 2M+4, 0) → (a+M+1, 1, 1, 2M+5, 0)
  apply stepStar_trans (c₂ := ⟨a+M+1, 1, 1, 2*M+5, 0⟩)
  · rw [show a + M + 2 = (a + M + 1) + 1 from by ring]
    step fm; ring_nf; finish
  -- R3R2R2 chain (b=1): (a+M+1, 1, 1, 2M+5, 0) →* (a+2M+3, 1, M+3, 1, 0)
  apply stepStar_trans (c₂ := ⟨a+2*M+3, 1, M+3, 1, 0⟩)
  · have h := @r3r2r2_chain_b1 (M+2) (a+M+1) 0 1
    rw [show 1 + 2 * (M + 2) = 2 * M + 5 from by ring,
        show 0 + 1 = 1 from by ring,
        show a + M + 1 + (M + 2) = a + 2 * M + 3 from by ring,
        show 0 + (M + 2) + 1 = M + 3 from by ring] at h
    exact h
  -- R3: (a+2M+3, 1, M+3, 1, 0) → (a+2M+4, 1, M+2, 1, 2)
  -- R2: → (a+2M+4, 1, M+3, 0, 1)
  apply stepStar_trans (c₂ := ⟨a+2*M+4, 1, M+3, 0, 1⟩)
  · rw [show M + 3 = (M + 2) + 1 from by ring]
    step fm; step fm; ring_nf; finish
  -- R3 drain (b=1): (a+2M+4, 1, M+3, 0, 1) →* (a+3M+7, 1, 0, 0, 2M+7)
  have h := @r3_drain_b1 (M+3) (a+2*M+4) 1
  rw [show a + 2 * M + 4 + (M + 3) = a + 3 * M + 7 from by ring,
      show 1 + 2 * (M + 3) = 2 * M + 7 from by ring] at h
  exact h

-- Main transition: (a+1, 0, 0, 2*M+2, 0) ⊢⁺ (a+2*M+3, 0, 0, 2*M+8, 0)
theorem main_trans : ⟨a+1, 0, 0, 2*M+2, 0⟩ [fm]⊢⁺ ⟨a+2*M+3, 0, 0, 2*M+8, 0⟩ := by
  -- Phase 1: → (a+2M+4, 0, 0, 0, 2M+5)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+2*M+4, 0, 0, 0, 2*M+5⟩)
  · exact phase1_b0
  -- Phase 2 (R4 drain): → (a+2M+4, 2M+5, 0, 0, 0)
  apply step_stepStar_stepPlus (c₂ := ⟨a+2*M+4, 1, 0, 0, 2*M+4⟩)
  · show fm ⟨a + 2 * M + 4, 0, 0, 0, (2 * M + 4) + 1⟩ = some ⟨a + 2 * M + 4, 1, 0, 0, 2 * M + 4⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨a+2*M+4, 2*M+5, 0, 0, 0⟩)
  · have h := @r4_drain (2*M+4) (a+2*M+4) 1
    rw [show 1 + (2 * M + 4) = 2 * M + 5 from by ring] at h
    exact h
  -- Phase 3 (R5+R1 chain): → (a+M+2, 1, 0, 2M+4, 0)
  apply stepStar_trans (c₂ := ⟨a+M+2, 1, 0, 2*M+4, 0⟩)
  · have h := @r5r1_chain (M+2) (a+M+2) 1 0
    rw [show a + M + 2 + (M + 2) = a + 2 * M + 4 from by ring,
        show 1 + 2 * (M + 2) = 2 * M + 5 from by ring,
        show 0 + 2 * (M + 2) = 2 * M + 4 from by ring] at h
    exact h
  -- Phase 4: → (a+3M+7, 1, 0, 0, 2M+7)
  apply stepStar_trans (c₂ := ⟨a+3*M+7, 1, 0, 0, 2*M+7⟩)
  · exact phase4_b1
  -- Phase 5 (R4 drain): → (a+3M+7, 2M+8, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨a+3*M+7, 2*M+8, 0, 0, 0⟩)
  · have h := @r4_drain (2*M+7) (a+3*M+7) 1
    rw [show 1 + (2 * M + 7) = 2 * M + 8 from by ring] at h
    exact h
  -- Phase 6 (R5+R1 chain): → (a+2M+3, 0, 0, 2M+8, 0)
  have h := @r5r1_chain (M+4) (a+2*M+3) 0 0
  rw [show a + 2 * M + 3 + (M + 4) = a + 3 * M + 7 from by ring,
      show 0 + 2 * (M + 4) = 2 * M + 8 from by ring] at h
  exact stepStar_trans h (by finish)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 6, 0⟩) (by execute fm 28)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, M⟩ ↦ ⟨a+1, 0, 0, 2*M+2, 0⟩) ⟨0, 2⟩
  intro ⟨a, M⟩; exact ⟨⟨a + 2*M + 2, M + 3⟩, main_trans⟩
