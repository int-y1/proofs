import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #372: [2/15, 9/14, 275/2, 49/55, 2/7]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  0
-1  0  2  0  1
 0  0 -1  2 -1
 1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_372

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- Rule 4 repeated: (0, 0, c+k, d, e+k) →* (0, 0, c, d+2*k, e)
theorem rule4_chain : ∀ k c d e, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Rule 3 repeated: (a+k, 0, c, 0, e) →* (a, 0, c+2*k, 0, e+k)
theorem rule3_chain : ∀ k a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Drain d via alternating rule2/rule5: (1, b, 0, 2*k, 0) →* (1, b+2*k, 0, 0, 0)
theorem drain_d : ∀ k b, ⟨1, b, 0, 2*k, 0⟩ [fm]⊢* ⟨1, b+2*k, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- Phase 3a: groups of 3 steps (rule3, rule1, rule1)
theorem phase3a_chain : ∀ k a b e, ⟨a+1, b+2*k, 0, 0, e⟩ [fm]⊢* ⟨a+k+1, b, 0, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a b e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
      show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  step fm
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 3b: (a+1, 1, 0, 0, e) →* (a+1, 0, 1, 0, e+1) in 2 steps
theorem phase3b : ⟨a+1, 1, 0, 0, e⟩ [fm]⊢* ⟨a+1, 0, 1, 0, e+1⟩ := by
  step fm
  step fm
  finish

-- Combined phase 2-3: (0, 0, 1, 2*(2*n+1)+2, 0) →⁺ (0, 0, 4*n+5, 0, 4*n+4)
theorem phase23 (n : ℕ) : ⟨0, 0, 1, 2*(2*n+1)+2, 0⟩ [fm]⊢⁺ ⟨0, 0, 4*n+5, 0, 4*n+4⟩ := by
  -- 3 initial steps: rule5, rule2, rule1
  step fm
  step fm
  step fm
  -- Now at (1, 1, 0, 2*(2*n+1), 0)
  -- drain_d: →* (1, 1+2*(2*n+1), 0, 0, 0)
  apply stepStar_trans (drain_d (2*n+1) 1)
  -- Phase 3a: (1, 1+2*(2*n+1), 0, 0, 0) →* (2*n+2, 1, 0, 0, 2*n+1)
  rw [show (1 : ℕ) = 0 + 1 from by omega]
  apply stepStar_trans (phase3a_chain (2*n+1) 0 1 0)
  simp only [Nat.zero_add]
  -- Phase 3b: ((2*n+1)+1, 1, 0, 0, 2*n+1) →* ((2*n+1)+1, 0, 1, 0, (2*n+1)+1)
  apply stepStar_trans phase3b
  -- Phase 3c: rule3_chain
  have h5 := rule3_chain (2*n+2) 0 1 (2*n+2)
  simp only [Nat.zero_add] at h5
  rw [show (2*n+1) + 1 = 2*n+2 from by omega]
  rw [show 1 + 2 * (2 * n + 2) = 4*n+5 from by omega,
      show (2*n+2) + (2*n+2) = 4*n+4 from by omega] at h5
  exact h5

-- Main transition: (0, 0, 2*n+3, 0, 2*n+2) →⁺ (0, 0, 4*n+5, 0, 4*n+4)
theorem main_trans (n : ℕ) : ⟨0, 0, 2*n+3, 0, 2*n+2⟩ [fm]⊢⁺ ⟨0, 0, 4*n+5, 0, 4*n+4⟩ := by
  -- Phase 1: rule4_chain with k=2*n+2
  have h1 := rule4_chain (2*n+2) 1 0 0
  simp only [Nat.zero_add] at h1
  rw [show (2 : ℕ)*n+3 = 1+(2*n+2) from by omega,
      show (2 : ℕ)*n+2 = 0+(2*n+2) from by omega]
  simp only [Nat.zero_add]
  apply stepStar_stepPlus_stepPlus h1
  rw [show 2 * (2 * n + 2) = 2 * (2 * n + 1) + 2 from by omega]
  exact phase23 n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, 2*n+3, 0, 2*n+2⟩) 0
  intro n
  refine ⟨2*n+1, ?_⟩
  show ⟨0, 0, 2*n+3, 0, 2*n+2⟩ [fm]⊢⁺ ⟨0, 0, 2*(2*n+1)+3, 0, 2*(2*n+1)+2⟩
  rw [show 2*(2*n+1)+3 = 4*n+5 from by omega,
      show 2*(2*n+1)+2 = 4*n+4 from by omega]
  exact main_trans n

end Sz22_2003_unofficial_372
