import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #32: [35/6, 121/2, 4/55, 3/7, 35/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_32

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 repeated: d → b (when a=0, c=0)
theorem d_to_b (e : ℕ) : ∀ k b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3R2R2 chain: k rounds
-- (0, 0, c+k, d, e+k) ->* (0, 0, c, d, e+4*k)
theorem r3r2r2_chain : ∀ k, ∀ e c d, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d, e+4*k⟩ := by
  intro k; induction' k with k h <;> intro e c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R3
  step fm  -- R2
  step fm  -- R2
  -- State: (0, 0, c+k, d, e+k+4)
  rw [show e + k + 2 + 2 = (e + 4) + k from by ring]
  refine stepStar_trans (h (e + 4) c d) ?_
  ring_nf; finish

-- R3R1R1 chain: k rounds
-- (0, b+2*k, c+1, d, e+k) ->* (0, b, c+1+k, d+2*k, e)
theorem r3r1r1_chain : ∀ k, ∀ e b c d, ⟨0, b+2*k, c+1, d, e+k⟩ [fm]⊢* ⟨0, b, c+1+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro e b c d
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R3: (2, b+2k+2, c, d, e+k)
  rw [show b + 2 * k + 1 + 1 = (b + 2 * k) + 1 + 1 from by ring]
  step fm  -- R1: (1, b+2k+1, c+1, d+1, e+k)
  step fm  -- R1: (0, b+2k, c+2, d+2, e+k)
  rw [show c + 2 = (c + 1) + 1 from by ring]
  refine stepStar_trans (h e b (c + 1) (d + 2)) ?_
  ring_nf; finish

-- Main transition for even D+1=2K (K >= 1): (0,0,0,2K,F+2K+2) ⊢⁺ (0,0,0,2K+1,F+4K+4)
theorem main_trans_even (K : ℕ) (F : ℕ) :
    ⟨0, 0, 0, 2*K, F+2*K+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*K+1, F+4*K+4⟩ := by
  -- Phase 1: d_to_b
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*K, 0, 0, F+2*K+2⟩)
  · have h := d_to_b (F+2*K+2) (2*K) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*K, 1, 1, F+2*K+1⟩)
  · rw [show F + 2 * K + 2 = (F + 2 * K + 1) + 1 from by ring]
    show fm ⟨0, 2 * K, 0, 0, (F + 2 * K + 1) + 1⟩ = some ⟨0, 2 * K, 1, 1, F + 2 * K + 1⟩
    simp [fm]
  -- Phase 3: r3r1r1 K rounds
  -- (0, 2K, 1, 1, F+2K+1) ->* (0, 0, K+1, 2K+1, F+K+1)
  apply stepStar_trans (c₂ := ⟨0, 0, K+1, 2*K+1, F+K+1⟩)
  · have h := r3r1r1_chain K (F+K+1) 0 0 1
    rw [show 0 + 2 * K = 2 * K from by ring,
        show (F + K + 1) + K = F + 2 * K + 1 from by ring,
        show 0 + 1 + K = K + 1 from by ring,
        show 1 + 2 * K = 2 * K + 1 from by ring] at h
    exact h
  -- Phase 4: r3r2r2 K+1 rounds
  -- (0, 0, K+1, 2K+1, F+K+1) ->* (0, 0, 0, 2K+1, F+4K+4)
  have h := r3r2r2_chain (K+1) F 0 (2*K+1)
  rw [show 0 + (K + 1) = K + 1 from by ring,
      show F + (K + 1) = F + K + 1 from by ring,
      show F + 4 * (K + 1) = F + 4 * K + 4 from by ring] at h
  exact h

-- Main transition for odd D+1=2K+1 (K >= 0): (0,0,0,2K+1,F+2K+3) ⊢⁺ (0,0,0,2K+2,F+4K+6)
theorem main_trans_odd (K : ℕ) (F : ℕ) :
    ⟨0, 0, 0, 2*K+1, F+2*K+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*K+2, F+4*K+6⟩ := by
  -- Phase 1: d_to_b
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*K+1, 0, 0, F+2*K+3⟩)
  · have h := d_to_b (F+2*K+3) (2*K+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*K+1, 1, 1, F+2*K+2⟩)
  · rw [show F + 2 * K + 3 = (F + 2 * K + 2) + 1 from by ring]
    show fm ⟨0, 2 * K + 1, 0, 0, (F + 2 * K + 2) + 1⟩ = some ⟨0, 2 * K + 1, 1, 1, F + 2 * K + 2⟩
    simp [fm]
  -- Phase 3: r3r1r1 K rounds
  -- (0, 2K+1, 1, 1, F+2K+2) ->* (0, 1, K+1, 2K+1, F+K+2)
  apply stepStar_trans (c₂ := ⟨0, 1, K+1, 2*K+1, F+K+2⟩)
  · have h := r3r1r1_chain K (F+K+2) 1 0 1
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * K = 2 * K + 1 from by ring,
        show (F + K + 2) + K = F + 2 * K + 2 from by ring,
        show 0 + 1 + K = K + 1 from by ring] at h
    exact h
  -- Phase 3b: R3,R1,R2 partial round
  -- (0, 1, K+1, 2K+1, F+K+2) -> (0, 0, K+1, 2K+2, F+K+3)
  apply stepStar_trans (c₂ := ⟨0, 0, K+1, 2*K+2, F+K+3⟩)
  · rw [show F + K + 2 = (F + K + 1) + 1 from by ring]
    step fm  -- R3: (2, 1, K, 2K+1, F+K+1)
    step fm  -- R1: (1, 0, K+1, 2K+2, F+K+1)
    step fm  -- R2: (0, 0, K+1, 2K+2, F+K+3)
    ring_nf; finish
  -- Phase 4: r3r2r2 K+1 rounds
  -- (0, 0, K+1, 2K+2, F+K+3) ->* (0, 0, 0, 2K+2, F+4K+6)
  have h := r3r2r2_chain (K+1) (F+2) 0 (2*K+2)
  rw [show 0 + (K + 1) = K + 1 from by ring,
      show (F + 2) + (K + 1) = F + K + 3 from by ring,
      show (F + 2) + 4 * (K + 1) = F + 4 * K + 6 from by ring] at h
  exact h

-- Combine even and odd cases
theorem main_trans (D F : ℕ) :
    ⟨0, 0, 0, D+1, F+D+3⟩ [fm]⊢⁺ ⟨0, 0, 0, D+2, F+2*D+6⟩ := by
  rcases Nat.even_or_odd D with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- D = 2K, D+1 = 2K+1 (odd)
    subst hK
    rw [show K + K + 1 = 2 * K + 1 from by ring,
        show F + (K + K) + 3 = F + 2 * K + 3 from by ring,
        show (K + K) + 2 = 2 * K + 2 from by ring,
        show F + 2 * (K + K) + 6 = F + 4 * K + 6 from by ring]
    exact main_trans_odd K F
  · -- D = 2K+1, D+1 = 2(K+1) (even)
    subst hK
    rw [show 2 * K + 1 + 1 = 2 * (K + 1) from by ring,
        show F + (2 * K + 1) + 3 = F + 2 * (K + 1) + 2 from by ring,
        show 2 * K + 1 + 2 = 2 * (K + 1) + 1 from by ring,
        show F + 2 * (2 * K + 1) + 6 = F + 4 * (K + 1) + 4 from by ring]
    exact main_trans_even (K+1) F

theorem nonhalt : ¬halts fm c₀ := by
  -- c₀ = (1, 0, 0, 0, 0) reaches (0, 0, 0, 1, 4) in 5 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 4⟩) (by execute fm 5)
  -- (0, 0, 0, 1, 4) = C(0, 1) where C(D, F) = (0, 0, 0, D+1, F+D+3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨D, F⟩ ↦ ⟨0, 0, 0, D+1, F+D+3⟩) ⟨0, 1⟩
  intro ⟨D, F⟩
  refine ⟨⟨D+1, F+D+2⟩, ?_⟩
  show ⟨0, 0, 0, D+1, F+D+3⟩ [fm]⊢⁺ ⟨0, 0, 0, D+1+1, F+D+2+(D+1)+3⟩
  rw [show D + 1 + 1 = D + 2 from by ring,
      show F + D + 2 + (D + 1) + 3 = F + 2 * D + 6 from by ring]
  exact main_trans D F
