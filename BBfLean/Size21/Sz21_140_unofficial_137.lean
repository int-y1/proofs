import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #137: [9/35, 22/5, 25/33, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  0
 1  0 -1  0  1
 0 -1  2  0 -1
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_137

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 chain: e → d (when c=0, b=0)
theorem r4_chain : ∀ k, ∀ a d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d+k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; exists 0
  | succ k ih =>
    intro a d
    rw [show (k + 1) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Phase B: interleaved R3,R2,R2 drain. Each round: a+=2, b-=1, e+=1.
theorem phase_b : ∀ k, ∀ a b e, ⟨a, b+k, 0, 0, e+1⟩ [fm]⊢* ⟨a+2*k, b, 0, 0, e+1+k⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R2
    step fm  -- R2
    rw [show e + 2 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- D-drain step: 5 steps consume 3 from d, add 5 to b, subtract 1 from a
theorem d_drain_step : ∀ a b d, ⟨a+1, b, 0, d+3, 0⟩ [fm]⊢* ⟨a, b+5, 0, d, 0⟩ := by
  intro a b d
  rw [show d + 3 = (d + 2) + 1 from by ring]
  step fm  -- R5
  step fm  -- R1
  step fm  -- R3
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm  -- R1
  step fm  -- R1
  ring_nf; finish

-- D-drain with remainder
theorem d_drain_rem : ∀ k, ∀ a b r, ⟨a+k, b, 0, r + 3*k, 0⟩ [fm]⊢* ⟨a, b+5*k, 0, r, 0⟩ := by
  intro k; induction k with
  | zero => intro a b r; exists 0
  | succ k ih =>
    intro a b r
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show r + 3 * (k + 1) = (r + 3 * k) + 3 from by ring]
    apply stepStar_trans (d_drain_step _ _ _)
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Remainder 0: (A+1, B, 0, 0, 0) →⁺ (A+2*B+1, 0, 0, B+2, 0)
theorem rem0 : ∀ A B, ⟨A+1, B, 0, 0, 0⟩ [fm]⊢⁺ ⟨A+2*B+1, 0, 0, B+2, 0⟩ := by
  intro A B
  apply step_stepStar_stepPlus
  · show fm ⟨A + 1, B, 0, 0, 0⟩ = some ⟨A, B, 1, 0, 1⟩; simp [fm]
  -- R2 (c=1, d=0): (A+1, B, 0, 0, 2)
  step fm
  -- Phase B: (A+1, B, 0, 0, 2) = (A+1, 0+B, 0, 0, 1+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨A + 1 + 2 * B, 0, 0, 0, 1 + 1 + B⟩)
  · have h := phase_b B (A + 1) 0 1
    simp only [Nat.zero_add] at h; exact h
  -- Phase C: r4_chain
  · have h := r4_chain (1 + 1 + B) (A + 1 + 2 * B) 0
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish

-- Remainder 1: (A+1, B, 0, 1, 0) →⁺ (A+2*B+4, 0, 0, B+3, 0)
theorem rem1 : ∀ A B, ⟨A+1, B, 0, 1, 0⟩ [fm]⊢⁺ ⟨A+2*B+4, 0, 0, B+3, 0⟩ := by
  intro A B
  apply step_stepStar_stepPlus
  · show fm ⟨A + 1, B, 0, 1, 0⟩ = some ⟨A, B, 1, 1, 1⟩; simp [fm]
  step fm  -- R1: (A, B+2, 0, 0, 1)
  step fm  -- R3: (A, B+1, 2, 0, 0)
  step fm  -- R2: (A+1, B+1, 1, 0, 1)
  step fm  -- R2: (A+2, B+1, 0, 0, 2)
  -- Phase B: (A+2, B+1, 0, 0, 2) = (A+2, 0+(B+1), 0, 0, 1+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨A + 2 + 2 * (B + 1), 0, 0, 0, 1 + 1 + (B + 1)⟩)
  · have h := phase_b (B + 1) (A + 2) 0 1
    simp only [Nat.zero_add] at h; exact h
  · have h := r4_chain (1 + 1 + (B + 1)) (A + 2 + 2 * (B + 1)) 0
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish

-- Remainder 2: (A+1, B, 0, 2, 0) →⁺ (A+2*B+7, 0, 0, B+4, 0)
theorem rem2 : ∀ A B, ⟨A+1, B, 0, 2, 0⟩ [fm]⊢⁺ ⟨A+2*B+7, 0, 0, B+4, 0⟩ := by
  intro A B
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨A + 1, B, 0, 0 + 1 + 1, 0⟩ = some ⟨A, B, 1, 0 + 1 + 1, 1⟩; simp [fm]
  step fm  -- R1: (A, B+2, 0, 1, 1)
  step fm  -- R3: (A, B+1, 2, 1, 0)
  step fm  -- R1: (A, B+3, 1, 0, 0)
  step fm  -- R2: (A+1, B+3, 0, 0, 1)
  -- Phase B: (A+1, B+3, 0, 0, 1) = (A+1, 0+(B+3), 0, 0, 0+1)
  apply stepStar_trans (c₂ := ⟨A + 1 + 2 * (B + 3), 0, 0, 0, 0 + 1 + (B + 3)⟩)
  · have h := phase_b (B + 3) (A + 1) 0 0
    simp only [Nat.zero_add] at h; exact h
  · have h := r4_chain (0 + 1 + (B + 3)) (A + 1 + 2 * (B + 3)) 0
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish

-- Full transition for d ≡ 0 (mod 3), d = 3*(K+1) (K ≥ 0):
theorem trans_mod0 : ∀ K, ∀ A, ⟨A+K+2, 0, 0, 3*(K+1), 0⟩ [fm]⊢⁺ ⟨A+10*K+11, 0, 0, 5*K+7, 0⟩ := by
  intro K A
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨A+1, 0+5*(K+1), 0, 0, 0⟩)
  · rw [show A + K + 2 = (A + 1) + (K + 1) from by ring,
        show 3 * (K + 1) = 0 + 3 * (K + 1) from by ring]
    exact d_drain_rem (K + 1) (A + 1) 0 0
  · rw [show 0 + 5 * (K + 1) = 5 * (K + 1) from by ring]
    have h := rem0 A (5 * (K + 1))
    refine stepPlus_stepStar_stepPlus h ?_; ring_nf; finish

-- Full transition for d ≡ 1 (mod 3), d = 3*K+1 (K ≥ 0):
theorem trans_mod1 : ∀ K, ∀ A, ⟨A+K+1, 0, 0, 3*K+1, 0⟩ [fm]⊢⁺ ⟨A+10*K+4, 0, 0, 5*K+3, 0⟩ := by
  intro K A
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨A+1, 0+5*K, 0, 1, 0⟩)
  · rw [show A + K + 1 = (A + 1) + K from by ring,
        show 3 * K + 1 = 1 + 3 * K from by ring]
    exact d_drain_rem K (A + 1) 0 1
  · rw [show 0 + 5 * K = 5 * K from by ring]
    have h := rem1 A (5 * K)
    refine stepPlus_stepStar_stepPlus h ?_; ring_nf; finish

-- Full transition for d ≡ 2 (mod 3), d = 3*K+2 (K ≥ 0):
theorem trans_mod2 : ∀ K, ∀ A, ⟨A+K+1, 0, 0, 3*K+2, 0⟩ [fm]⊢⁺ ⟨A+10*K+7, 0, 0, 5*K+4, 0⟩ := by
  intro K A
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨A+1, 0+5*K, 0, 2, 0⟩)
  · rw [show A + K + 1 = (A + 1) + K from by ring,
        show 3 * K + 2 = 2 + 3 * K from by ring]
    exact d_drain_rem K (A + 1) 0 2
  · rw [show 0 + 5 * K = 5 * K from by ring]
    have h := rem2 A (5 * K)
    refine stepPlus_stepStar_stepPlus h ?_; ring_nf; finish

-- Main non-halting theorem
theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) reaches (7, 0, 0, 4, 0) in 22 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 4, 0⟩) (by execute fm 22)
  -- Use progress_nonhalt with P(q) = ∃ a d, q = (a, 0, 0, d, 0) ∧ d ≥ 2 ∧ a ≥ d / 3 + 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 2 ∧ a ≥ d / 3 + 1)
  · intro q ⟨a, d, hq, hd, ha⟩; subst hq
    rcases (show d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 from by omega) with h0 | h1 | h2
    · -- d ≡ 0 mod 3: d = 3*(K+1) since d ≥ 2 and d % 3 = 0 means d ≥ 3
      obtain ⟨K, rfl⟩ : ∃ K, d = 3 * (K + 1) := ⟨d / 3 - 1, by omega⟩
      have haK : a ≥ K + 2 := by omega
      obtain ⟨A, rfl⟩ : ∃ A, a = A + K + 2 := ⟨a - K - 2, by omega⟩
      exact ⟨_, ⟨A + 10 * K + 11, 5 * K + 7, rfl, by omega, by omega⟩, trans_mod0 K A⟩
    · -- d ≡ 1 mod 3: d = 3*K+1
      obtain ⟨K, rfl⟩ : ∃ K, d = 3 * K + 1 := ⟨d / 3, by omega⟩
      have haK : a ≥ K + 1 := by omega
      obtain ⟨A, rfl⟩ : ∃ A, a = A + K + 1 := ⟨a - K - 1, by omega⟩
      exact ⟨_, ⟨A + 10 * K + 4, 5 * K + 3, rfl, by omega, by omega⟩, trans_mod1 K A⟩
    · -- d ≡ 2 mod 3: d = 3*K+2
      obtain ⟨K, rfl⟩ : ∃ K, d = 3 * K + 2 := ⟨d / 3, by omega⟩
      have haK : a ≥ K + 1 := by omega
      obtain ⟨A, rfl⟩ : ∃ A, a = A + K + 1 := ⟨a - K - 1, by omega⟩
      exact ⟨_, ⟨A + 10 * K + 7, 5 * K + 4, rfl, by omega, by omega⟩, trans_mod2 K A⟩
  · exact ⟨7, 4, rfl, by omega, by omega⟩

end Sz21_140_unofficial_137
