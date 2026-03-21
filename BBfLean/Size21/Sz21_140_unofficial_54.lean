import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #54: [35/6, 605/2, 4/77, 3/5, 2/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_54

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- Phase 1: R4 repeated: c → b (when a=0, d=0)
theorem c_to_b : ∀ k, ∀ b c e, ⟨0, b, c+k, 0, e⟩ [fm]⊢* ⟨0, b+k, c, 0, e⟩ := by
  intro k; induction' k with k h <;> intro b c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3R2R2 chain: each round (0,0,c,d+1,e+1) → (0,0,c+2,d,e+4)
-- Parameterized: (0, 0, c, d+k, e+k) →* (0, 0, c+2*k, d, e+4*k)
theorem r3r2r2_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d+k, e+k⟩ [fm]⊢* ⟨0, 0, c+2*k, d, e+4*k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R3: (0, 0, c, (d+k)+1, (e+k)+1) → (2, 0, c, d+k, e+k)
  step fm  -- R2: (2, 0, c, d+k, e+k) → (1, 0, c+1, d+k, e+k+2)
  step fm  -- R2: (1, 0, c+1, d+k, e+k+2) → (0, 0, c+2, d+k, e+k+4)
  rw [show e + k + 2 + 2 = (e + 4) + k from by ring,
      show c + 1 + 1 = c + 2 from by ring]
  apply stepStar_trans (h (c+2) d (e+4))
  ring_nf; finish

-- R1R1R3 chain: each round (2, b'+2, c', d', e'+1) → (2, b', c'+2, d'+1, e')
-- Parameterized: (2, b+2*k, c, d, e+k) →* (2, b, c+2*k, d+k, e)
theorem r1r1r3_chain : ∀ k, ∀ b c d e, ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+2*k, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro b c d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R1: (2, (b+2k)+1+1, c, d, (e+k)+1) → (1, (b+2k)+1, c+1, d+1, (e+k)+1)
  rw [show (e + k) + 1 = (e + k + 1) from by ring]
  step fm  -- R1: (1, (b+2k)+1, c+1, d+1, e+k+1) → (0, b+2k, c+2, d+2, e+k+1)
  step fm  -- R3: (0, b+2k, c+2, d+2, e+k+1) → (2, b+2k, c+2, d+1, e+k)
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Middle phase for odd b = 2m+1: (0, 2m+1, 0, 0, 2m+2) →⁺ (0, 0, 4m+3, 0, 4m+4)
theorem middle_odd (m : ℕ) : ⟨0, 2*m+1, 0, 0, 2*m+2⟩ [fm]⊢⁺ ⟨0, 0, 4*m+3, 0, 4*m+4⟩ := by
  -- R5: (0, 2m+1, 0, 0, 2m+2) → (1, 2m+1, 0, 0, 2m+1)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2*m+1, 0, 0, 2*m+1⟩)
  · show fm ⟨0, 2*m+1, 0, 0, (2*m+1)+1⟩ = some ⟨1, 2*m+1, 0, 0, 2*m+1⟩; simp [fm]
  -- R1: (1, 2m+1, 0, 0, 2m+1) → (0, 2m, 1, 1, 2m+1)
  apply stepStar_trans (c₂ := ⟨0, 2*m, 1, 1, 2*m+1⟩)
  · rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
    apply step_stepStar
    show fm ⟨0+1, (2*m)+1, 0, 0, 2*m+1⟩ = some ⟨0, 2*m, 1, 1, 2*m+1⟩; simp [fm]
  -- R3: (0, 2m, 1, 1, 2m+1) → (2, 2m, 1, 0, 2m)
  apply stepStar_trans (c₂ := ⟨2, 2*m, 1, 0, 2*m⟩)
  · rw [show 2 * m + 1 = (2*m) + 1 from by ring]
    apply step_stepStar
    show fm ⟨0, 2*m, 1, 0+1, (2*m)+1⟩ = some ⟨2, 2*m, 1, 0, 2*m⟩; simp [fm]
  -- R1R1R3 chain: m rounds from (2, 2m, 1, 0, 2m) → (2, 0, 2m+1, m, m)
  -- Use: (2, b+2*k, c, d, e+k) →* (2, b, c+2*k, d+k, e) with b=0, k=m, c=1, d=0, e=m
  apply stepStar_trans (c₂ := ⟨2, 0, 2*m+1, m, m⟩)
  · have h := @r1r1r3_chain m 0 1 0 m
    rw [show 0 + 2 * m = 2 * m from by ring,
        show m + m = 2 * m from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring,
        show 0 + m = m from by ring] at h
    exact h
  -- R2: (2, 0, 2m+1, m, m) → (1, 0, 2m+2, m, m+2)
  apply stepStar_trans (c₂ := ⟨1, 0, 2*m+2, m, m+2⟩)
  · apply step_stepStar
    show fm ⟨(1)+1, 0, 2*m+1, m, m⟩ = some ⟨1, 0, 2*m+2, m, m+2⟩; simp [fm]
  -- R2: (1, 0, 2m+2, m, m+2) → (0, 0, 2m+3, m, m+4)
  apply stepStar_trans (c₂ := ⟨0, 0, 2*m+3, m, m+4⟩)
  · apply step_stepStar
    show fm ⟨(0)+1, 0, 2*m+2, m, m+2⟩ = some ⟨0, 0, 2*m+3, m, m+4⟩; simp [fm]
  -- R3R2R2 chain: m rounds from (0, 0, 2m+3, m, m+4) → (0, 0, 4m+3, 0, 4m+4)
  -- Use: (0, 0, c, d+k, e+k) →* (0, 0, c+2*k, d, e+4*k) with c=2m+3, d=0, k=m, e=4
  have h := @r3r2r2_chain m (2*m+3) 0 4
  rw [show 0 + m = m from by ring,
      show 4 + m = m + 4 from by ring,
      show 2 * m + 3 + 2 * m = 4 * m + 3 from by ring,
      show 4 + 4 * m = 4 * m + 4 from by ring] at h
  exact h

-- Middle phase for even b = 2m (m >= 1): (0, 2*m, 0, 0, 2*m+1) →⁺ (0, 0, 4*m+1, 0, 4*m+2)
-- We handle m = 0 separately (it's trivial since b=0 doesn't arise in our proof)
theorem middle_even (m : ℕ) : ⟨0, 2*(m+1), 0, 0, 2*(m+1)+1⟩ [fm]⊢⁺ ⟨0, 0, 4*(m+1)+1, 0, 4*(m+1)+2⟩ := by
  -- R5: → (1, 2m+2, 0, 0, 2m+2)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2*(m+1), 0, 0, 2*(m+1)⟩)
  · rw [show 2 * (m + 1) + 1 = (2*(m+1)) + 1 from by ring]
    show fm ⟨0, 2*(m+1), 0, 0, (2*(m+1))+1⟩ = some ⟨1, 2*(m+1), 0, 0, 2*(m+1)⟩; simp [fm]
  -- R1: → (0, 2m+1, 1, 1, 2m+2)
  apply stepStar_trans (c₂ := ⟨0, 2*m+1, 1, 1, 2*(m+1)⟩)
  · rw [show 2 * (m + 1) = (2 * m + 1) + 1 from by ring]
    apply step_stepStar
    show fm ⟨0+1, (2*m+1)+1, 0, 0, 2*(m+1)⟩ = some ⟨0, 2*m+1, 1, 1, 2*(m+1)⟩; simp [fm]
  -- R3: → (2, 2m+1, 1, 0, 2m+1)
  apply stepStar_trans (c₂ := ⟨2, 2*m+1, 1, 0, 2*m+1⟩)
  · rw [show 2 * (m + 1) = (2*m+1) + 1 from by ring]
    apply step_stepStar
    show fm ⟨0, 2*m+1, 1, 0+1, (2*m+1)+1⟩ = some ⟨2, 2*m+1, 1, 0, 2*m+1⟩; simp [fm]
  -- R1R1R3 chain: m rounds from (2, 2m+1, 1, 0, 2m+1) → (2, 1, 2m+1, m, m+1)
  -- Use: (2, b+2*k, c, d, e+k) →* (2, b, c+2*k, d+k, e) with b=1, k=m, c=1, d=0, e=m+1
  apply stepStar_trans (c₂ := ⟨2, 1, 2*m+1, m, m+1⟩)
  · have h := @r1r1r3_chain m 1 1 0 (m+1)
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- R1: (2, 1, 2m+1, m, m+1) → (1, 0, 2m+2, m+1, m+1)
  apply stepStar_trans (c₂ := ⟨1, 0, 2*m+2, m+1, m+1⟩)
  · apply step_stepStar
    show fm ⟨(1)+1, (0)+1, 2*m+1, m, m+1⟩ = some ⟨1, 0, 2*m+2, m+1, m+1⟩; simp [fm]
  -- R2: (1, 0, 2m+2, m+1, m+1) → (0, 0, 2m+3, m+1, m+3)
  apply stepStar_trans (c₂ := ⟨0, 0, 2*m+3, m+1, m+3⟩)
  · apply step_stepStar
    show fm ⟨(0)+1, 0, 2*m+2, m+1, m+1⟩ = some ⟨0, 0, 2*m+3, m+1, m+3⟩; simp [fm]
  -- R3R2R2 chain: (m+1) rounds from (0, 0, 2m+3, m+1, m+3) → (0, 0, 4m+5, 0, 4m+7)
  -- Use: (0, 0, c, d+k, e+k) →* (0, 0, c+2*k, d, e+4*k) with c=2m+3, d=0, k=m+1, e=2
  have h := @r3r2r2_chain (m+1) (2*m+3) 0 2
  rw [show 0 + (m + 1) = m + 1 from by ring,
      show 2 + (m + 1) = m + 3 from by ring,
      show 2 * m + 3 + 2 * (m + 1) = 4 * (m + 1) + 1 from by ring,
      show 2 + 4 * (m + 1) = 4 * (m + 1) + 2 from by ring] at h
  exact h

-- Main transition: (0, 0, c, 0, c+1) ⊢⁺ (0, 0, 2*c+1, 0, 2*c+2)
theorem main_trans (c : ℕ) : ⟨0, 0, c+1, 0, c+2⟩ [fm]⊢⁺ ⟨0, 0, 2*c+3, 0, 2*c+4⟩ := by
  -- Phase 1: c_to_b: (0, 0, c+1, 0, c+2) →* (0, c+1, 0, 0, c+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, c+1, 0, 0, c+2⟩)
  · have h := @c_to_b (c+1) 0 0 (c+2)
    rw [show 0 + (c + 1) = c + 1 from by ring] at h
    exact h
  -- Phase 2: middle phase with parity split on c+1
  rcases Nat.even_or_odd (c+1) with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- c+1 = 2K, K >= 1 (since c+1 >= 1)
    -- (0, 2K, 0, 0, 2K+1) →⁺ (0, 0, 4K+1, 0, 4K+2)
    -- 2K = c+1, so K >= 1, write K = K'+1
    have hK_pos : K ≥ 1 := by omega
    obtain ⟨K', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
    rw [show c + 1 = 2 * (K' + 1) from by omega,
        show c + 2 = 2 * (K' + 1) + 1 from by omega]
    have h := middle_even K'
    rw [show 2 * c + 3 = 4 * (K' + 1) + 1 from by omega,
        show 2 * c + 4 = 4 * (K' + 1) + 2 from by omega]
    exact h
  · -- c+1 = 2K+1
    -- (0, 2K+1, 0, 0, 2K+2) →⁺ (0, 0, 4K+3, 0, 4K+4)
    rw [show c + 1 = 2 * K + 1 from by omega,
        show c + 2 = 2 * K + 2 from by omega]
    have h := middle_odd K
    rw [show 2 * c + 3 = 4 * K + 3 from by omega,
        show 2 * c + 4 = 4 * K + 4 from by omega]
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1, 0, 0, 0, 0) reaches (0, 0, 1, 0, 2) in 1 step
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 1)
  -- Canonical form: (0, 0, c+1, 0, c+2) with c → 2c+1 (i.e., c+1 → 2c+3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun c ↦ ⟨0, 0, c+1, 0, c+2⟩) 0
  intro c; exact ⟨2*c+2, main_trans c⟩
