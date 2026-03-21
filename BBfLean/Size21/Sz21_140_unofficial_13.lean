import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #13: [1/6, 35/2, 4/55, 3/5, 242/21]

Vector representation:
```
-1 -1  0  0  0
-1  0  1  1  0
 2  0 -1  0 -1
 0  1 -1  0  0
 1 -1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_13

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- Phase 1: c → b
theorem c_to_b : ∀ k, ∀ b d, ⟨0, b, k, d, 0⟩ [fm]⊢* ⟨0, b+k, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Phase 2: R5+R1 pairs
theorem r5r1_pairs : ∀ k, ∀ d e, ⟨0, 2*k+1, 0, d+k+1, e⟩ [fm]⊢* ⟨1, 0, 0, d, e+2*k+2⟩ := by
  intro k; induction' k with k h <;> intro d e
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring,
        show d + (k + 1) + 1 = d + k + 1 + 1 from by ring]
    step fm
    step fm
    rw [show d + k + 1 = d + k + 1 from rfl]
    apply stepStar_trans (h d (e + 2))
    ring_nf; finish

-- Phase 3: R3+R2+R2 chain
theorem r3r2r2_chain : ∀ k, ∀ c d, ⟨0, 0, c+1, d, k⟩ [fm]⊢* ⟨0, 0, c+k+1, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    step fm
    step fm
    apply stepStar_trans (h (c + 1) (d + 2))
    ring_nf; finish

-- Main transition: (0, 0, 2n+3, d, 0) ⊢⁺ (0, 0, 2n+5, d+3n+7, 0)
theorem main_trans (n D : ℕ) : ⟨0, 0, 2*n+3, D+n+2, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*n+5, D+n+2+3*n+7, 0⟩ := by
  -- Phase 1: c_to_b
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*n+3, 0, D+n+2, 0⟩)
  · have h := c_to_b (2*n+3) 0 (D+n+2)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: r5r1_pairs
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2*n+2, 0, D+n+1, 2⟩)
  · show fm ⟨0, (2 * n + 2) + 1, 0, (D + n + 1) + 1, 0⟩ = some ⟨1, 2 * n + 2, 0, D + n + 1, 2⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 2*n+1, 0, D+n+1, 2⟩)
  · show ⟨1, (2 * n + 1) + 1, 0, D + n + 1, 2⟩ [fm]⊢* ⟨0, 2 * n + 1, 0, D + n + 1, 2⟩
    step fm; finish
  apply stepStar_trans (c₂ := ⟨1, 0, 0, D, 2*n+4⟩)
  · have h := r5r1_pairs n D 2
    rw [show 2 * n + 1 = 2 * n + 1 from rfl,
        show D + n + 1 = D + n + 1 from rfl] at h
    convert h using 2; ring_nf
  -- Phase 3: R2 then r3r2r2_chain
  apply stepStar_trans (c₂ := ⟨0, 0, 1, D+1, 2*n+4⟩)
  · step fm; finish
  have h := r3r2r2_chain (2*n+4) 0 (D+1)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 5, 0⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n D, q = ⟨0, 0, 2*n+3, D+n+2, 0⟩)
  · intro c ⟨n, D, hq⟩; subst hq
    exact ⟨_, ⟨n+1, D+3*n+6, by ring_nf⟩, main_trans n D⟩
  · exact ⟨0, 3, by ring_nf⟩
