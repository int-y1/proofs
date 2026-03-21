import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #28: [35/6, 11/2, 4/55, 3/7, 70/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 1  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_28

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d+1, e⟩
  | _ => none

-- Phase 1: R4 repeated: (0, b, 0, d+k, e) →* (0, b+k, 0, d, e)
theorem d_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d+k, (e : ℕ)⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Drain: R3,R2,R2 repeated: (0, 0, k, d, e+1) →* (0, 0, 0, d, e+k+1)
theorem drain : ∀ k, ∀ d e, ⟨0, 0, k, d, e+1⟩ [fm]⊢* ⟨0, 0, 0, d, e+k+1⟩ := by
  intro k; induction' k with k h <;> intro d e
  · exists 0
  -- (0, 0, k+1, d, e+1) →R3→ (2, 0, k, d, e) →R2→ (1, 0, k, d, e+1) →R2→ (0, 0, k, d, e+2)
  rw [show (k : ℕ) + 1 = k + 1 from rfl]
  step fm; step fm; step fm
  -- Now at (0, 0, k, d, (e+1)+1)
  apply stepStar_trans (h d (e + 1))
  ring_nf; finish

-- R3,R1,R1 rounds with extra b:
-- (0, b+2k, c+1, d, e+k) →* (0, b, c+1+k, d+2k, e)
theorem r3r1r1_rounds : ∀ k, ∀ b c d e, ⟨0, b+2*k, c+1, d, e+k⟩ [fm]⊢* ⟨0, b, c+1+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro b c d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  -- R3: (0, b+2k+2, c+1, d, e+k+1) → (2, b+2k+2, c, d, e+k)
  step fm
  -- R1: (2, b+2k+2, c, d, e+k) → (1, b+2k+1, c+1, d+1, e+k)
  rw [show (b + 2 * k + 1) + 1 = (b + 2 * k + 1) + 1 from rfl]
  step fm
  -- R1: (1, b+2k+1, c+1, d+1, e+k) → (0, b+2k, c+2, d+2, e+k)
  step fm
  -- (0, b+2k, (c+1)+1, d+2, e+k)
  apply stepStar_trans (h b (c + 1) (d + 2) e)
  ring_nf; finish

-- R3,R1,R2 tail when b=1:
-- (0, 1, c+1, d, e+1) →R3→ (2, 1, c, d, e) →R1→ (1, 0, c+1, d+1, e) →R2→ (0, 0, c+1, d+1, e+1)
theorem r3r1r2_tail : ⟨0, 1, (c : ℕ)+1, (d : ℕ), (e : ℕ)+1⟩ [fm]⊢* ⟨0, 0, c+1, d+1, e+1⟩ := by
  step fm; step fm; step fm; finish

-- Main transition for odd n=2K+1 (K≥0):
-- (0,0,0,2K+1,2K+2) →⁺ (0,0,0,2K+2,2K+3)
theorem main_trans_odd (K : ℕ) : ⟨0, 0, 0, 2*K+1, 2*K+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*K+2, 2*K+3⟩ := by
  -- Phase 1: R4 * (2K+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*K+1, 0, 0, 2*K+2⟩)
  · have h := @d_to_b (2*K+2) (2*K+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2*K+1, 1, 1, 2*K+1⟩)
  · show fm ⟨0, 2*K+1, 0, 0, (2*K+1)+1⟩ = some ⟨1, 2*K+1, 1, 1, 2*K+1⟩; simp [fm]
  -- Phase 3a: R1
  apply stepStar_trans (c₂ := ⟨0, 2*K, 2, 2, 2*K+1⟩)
  · rw [show (2 : ℕ) * K + 1 = (2 * K) + 1 from by ring]
    step fm; finish
  -- Phase 3b: R3,R1,R1 * K rounds (b=0+2K, c+1=2, d=2, e+K=K+1+K=2K+1)
  -- (0, 2K, 2, 2, 2K+1) →* (0, 0, K+2, 2+2K, K+1)
  apply stepStar_trans (c₂ := ⟨0, 0, K+2, 2+2*K, K+1⟩)
  · have h := r3r1r1_rounds K 0 1 2 (K+1)
    rw [show (K + 1) + K = 2 * K + 1 from by ring,
        show (0 : ℕ) + 2 * K = 2 * K from by ring] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  -- Phase 4: Drain (K+2) rounds: (0,0,K+2,2+2K,K+1) → (0,0,0,2K+2,2K+3)
  -- drain: (0,0,k,d,e+1) →* (0,0,0,d,e+k+1) with k=K+2, d=2+2K, e=K
  have h := drain (K+2) (2+2*K) K
  rw [show K + 1 = K + 1 from rfl] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Main transition for even n=2(K+1) (K≥0, so n≥2):
-- (0,0,0,2K+2,2K+3) →⁺ (0,0,0,2K+3,2K+4)
theorem main_trans_even (K : ℕ) : ⟨0, 0, 0, 2*(K+1), 2*(K+1)+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*(K+1)+1, 2*(K+1)+2⟩ := by
  -- Phase 1: R4 * 2(K+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*(K+1), 0, 0, 2*(K+1)+1⟩)
  · have h := @d_to_b (2*(K+1)+1) (2*(K+1)) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2*(K+1), 1, 1, 2*(K+1)⟩)
  · show fm ⟨0, 2*(K+1), 0, 0, (2*(K+1))+1⟩ = some ⟨1, 2*(K+1), 1, 1, 2*(K+1)⟩; simp [fm]
  -- Phase 3a: R1: (1,2K+2,1,1,2K+2) → (0,2K+1,2,2,2K+2)
  apply stepStar_trans (c₂ := ⟨0, 2*K+1, 2, 2, 2*(K+1)⟩)
  · rw [show (2 : ℕ) * (K + 1) = (2 * K + 1) + 1 from by ring]
    step fm; finish
  -- Phase 3b: R3,R1,R1 * K rounds with extra b=1
  -- r3r1r1_rounds K b c d e: (0, b+2K, c+1, d, e+K) →* (0, b, c+1+K, d+2K, e)
  -- b=1, c+1=2 so c=1, d=2, e+K = 2(K+1)-K = K+2
  -- (0, 1+2K, 2, 2, K+2+K) = (0, 2K+1, 2, 2, 2K+2)
  -- →* (0, 1, K+2, 2+2K, K+2)
  apply stepStar_trans (c₂ := ⟨0, 1, K+2, 2+2*K, K+2⟩)
  · have h := r3r1r1_rounds K 1 1 2 (K+2)
    rw [show (K + 2) + K = 2 * (K + 1) from by ring,
        show (1 : ℕ) + 2 * K = 2 * K + 1 from by ring] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  -- Phase 3c: R3,R1,R2 tail: (0, 1, K+2, 2+2K, K+2)
  -- Need form (0, 1, c+1, d, e+1): c+1=K+2 so c=K+1, d=2+2K, e+1=K+2 so e=K+1
  apply stepStar_trans (c₂ := ⟨0, 0, K+2, 3+2*K, K+2⟩)
  · have h := @r3r1r2_tail (K+1) (2+2*K) (K+1)
    rw [show (K + 1) + 1 = K + 2 from by ring,
        show (K + 1) + 1 = K + 2 from by ring] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  -- Phase 4: Drain (K+2) rounds: (0,0,K+2,3+2K,K+2) → (0,0,0,2K+3,2K+4)
  -- drain: (0,0,k,d,e+1) →* (0,0,0,d,e+k+1) with k=K+2, d=3+2K, e+1=K+2 so e=K+1
  have h := drain (K+2) (3+2*K) (K+1)
  rw [show (K + 1) + 1 = K + 2 from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Combine: (0,0,0,n+1,n+2) →⁺ (0,0,0,n+2,n+3)
theorem main_trans (n : ℕ) : ⟨0, 0, 0, n+1, n+2⟩ [fm]⊢⁺ ⟨0, 0, 0, n+2, n+3⟩ := by
  rcases Nat.even_or_odd (n+1) with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- n+1 = 2K (even), K ≥ 1 since n+1 ≥ 1
    -- n+1 = 2K means K ≥ 1, so K = K'+1
    rcases K with _ | K'
    · omega
    · -- n+1 = 2(K'+1), n = 2K'+1
      have hn : n + 1 = 2 * (K' + 1) := by omega
      rw [hn, show n + 2 = 2 * (K' + 1) + 1 from by omega,
          show n + 3 = 2 * (K' + 1) + 2 from by omega]
      exact main_trans_even K'
  · -- n+1 = 2K+1 (odd)
    have hn : n + 1 = 2 * K + 1 := by omega
    rw [hn, show n + 2 = 2 * K + 2 from by omega,
        show n + 3 = 2 * K + 3 from by omega]
    exact main_trans_odd K

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, 0, n+1, n+2⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩
