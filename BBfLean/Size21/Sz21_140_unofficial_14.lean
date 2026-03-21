import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #14: [1/6, 4/35, 55/2, 3/5, 98/33]

Vector representation:
```
-1 -1  0  0  0
 2  0 -1 -1  0
-1  0  1  0  1
 0  1 -1  0  0
 1 -1  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_14

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

-- Phase 1: R3 repeated: a → c,e (when b=0, d=0)
theorem a_to_ce : ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+k, 0, e+k⟩ := by
  have many_step : ∀ k a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+k, 0, e+k⟩ := by
    intro k; induction' k with k h <;> intro a c e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k a c e

-- Phase 2: R4 repeated: c → b (when a=0, d=0)
theorem c_to_b : ⟨0, b, c+k, 0, e⟩ [fm]⊢* ⟨0, b+k, c, 0, e⟩ := by
  have many_step : ∀ k b c, ⟨0, b, c+k, 0, e⟩ [fm]⊢* ⟨0, b+k, c, 0, e⟩ := by
    intro k; induction' k with k h <;> intro b c
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b c

-- Phase 3: (0, 2n+1, 0, d, e+n+1) →* (1, 0, 0, d+2n+2, e)
-- n R5+R1 pairs then one final R5
theorem phase3 : ∀ n, ∀ d e, ⟨0, 2*n+1, 0, d, e+n+1⟩ [fm]⊢* ⟨1, 0, 0, d+2*n+2, e⟩ := by
  intro n; induction' n with n h <;> intro d e
  · -- Base: (0, 1, 0, d, e+1) → R5 → (1, 0, 0, d+2, e)
    step fm; finish
  -- (0, 2*(n+1)+1, 0, d, e+(n+1)+1) = (0, 2n+3, 0, d, e+n+2)
  -- R5: (1, 2n+2, 0, d+2, e+n+1)
  -- R1: (0, 2n+1, 0, d+2, e+n+1)
  rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 from by ring,
      show e + (n + 1) + 1 = (e + n + 1) + 1 from by ring]
  step fm
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (h (d + 2) e)
  ring_nf; finish

-- Phase 4: R3+R2 alternating: (a+1, 0, 0, d+k, e) →* (a+1+k, 0, 0, d, e+k)
theorem r3r2_pairs : ∀ k, ∀ a d e, ⟨a+1, 0, 0, d+k, e⟩ [fm]⊢* ⟨a+1+k, 0, 0, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  -- State: (a+1, 0, 0, (d+k)+1, e)
  -- R3: (a, 0, 1, (d+k)+1, e+1)
  step fm
  -- R2: (a+2, 0, 0, d+k, e+1)
  step fm
  apply stepStar_trans (h (a + 1) d (e + 1))
  ring_nf; finish

-- Main transition: (2n+1, 0, 0, 0, e) →⁺ (2n+3, 0, 0, 0, e+3n+2)
theorem main_trans : ⟨2*n+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨2*n+3, 0, 0, 0, e+3*n+2⟩ := by
  -- Phase 1: R3 × (2n+1): (2n+1, 0, 0, 0, e) →* (0, 0, 2n+1, 0, e+2n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2*n+1, 0, e+2*n+1⟩)
  · have h := @a_to_ce 0 (2*n+1) 0 e
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 × (2n+1): (0, 0, 2n+1, 0, e+2n+1) →* (0, 2n+1, 0, 0, e+2n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*n+1, 0, 0, e+2*n+1⟩)
  · have h := @c_to_b 0 0 (2*n+1) (e+2*n+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: (0, 2n+1, 0, 0, e+2n+1) →* (1, 0, 0, 2n+2, e+n)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 0, 0, 2*n+2, e+n⟩)
  · have h := @phase3 n 0 (e + n)
    rw [show e + n + n + 1 = e + 2 * n + 1 from by ring,
        show 0 + 2 * n + 2 = 2 * n + 2 from by ring] at h
    exact h
  -- Phase 4: (1, 0, 0, 2n+2, e+n) →⁺ (2n+3, 0, 0, 0, e+3n+2)
  -- First R3: (1, 0, 0, 2n+2, e+n) → (0, 0, 1, 2n+2, e+n+1)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, 1, 2*n+2, e+n+1⟩)
  · show fm ⟨0 + 1, 0, 0, 2*n+2, e+n⟩ = some ⟨0, 0, 1, 2*n+2, e+n+1⟩; simp [fm]
  -- R2: (0, 0, 1, 2n+2, e+n+1) → (2, 0, 0, 2n+1, e+n+1)
  apply stepStar_trans (c₂ := ⟨2, 0, 0, 2*n+1, e+n+1⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring, show 2*n+2 = (2*n+1) + 1 from by ring]
    step fm; finish
  -- r3r2_pairs with a=1, k=2n+1, d=0: (2, 0, 0, 2n+1, e+n+1) →* (2n+3, 0, 0, 0, e+3n+2)
  have h := @r3r2_pairs (2*n+1) 1 0 (e+n+1)
  rw [show 1 + 1 = 2 from by ring,
      show 1 + 1 + (2 * n + 1) = 2 * n + 3 from by ring,
      show e + n + 1 + (2 * n + 1) = e + 3 * n + 2 from by ring,
      show 0 + (2 * n + 1) = 2 * n + 1 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨2*n+1, 0, 0, 0, e⟩) ⟨0, 0⟩
  intro ⟨n, e⟩; exact ⟨⟨n+1, e+3*n+2⟩, main_trans⟩
