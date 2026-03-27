import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #210: [1/6, 4/385, 35/2, 3/5, 242/21]

Vector representation:
```
-1 -1  0  0  0
 2  0 -1 -1 -1
-1  0  1  1  0
 0  1 -1  0  0
 1 -1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_210

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- Phase 1 (R3 repeated): a → c,d (with b=0, e=0)
theorem a_to_cd : ∀ k, ∀ c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + k, d + k, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Phase 2 (R4 repeated): c → b (when a=0, e=0)
theorem c_to_b : ∀ k, ∀ b d, ⟨0, b, k, d, 0⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Phase 3a (R5+R1 pair repeated): b,d → e (when a=0, c=0)
theorem r5r1_pairs : ∀ k, ∀ b d e, ⟨0, b + 2 * k, 0, d + k, e⟩ [fm]⊢* ⟨0, b, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 4 (R3+R2 repeated): increases a, decreases e (with b=0, d≥1)
theorem r3r2_loop : ∀ k, ∀ a d, ⟨a + 1, 0, 0, d + 1, k⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d + 1, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  rw [show (k + 1) = k + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Main transition: (2n+3, 0, 0, D, 0) →⁺ (2n+5, 0, 0, D+n+1, 0)
theorem main_trans : ∀ n D, ⟨2 * n + 3, 0, 0, D, 0⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, 0, D + n + 1, 0⟩ := by
  intro n D
  -- Phase 1: R3 × (2n+3): (2n+3, 0, 0, D, 0) →* (0, 0, 2n+3, D+2n+3, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2 * n + 3, D + (2 * n + 3), 0⟩)
  · have h := a_to_cd (2 * n + 3) 0 D
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 × (2n+3): (0, 0, 2n+3, D+2n+3, 0) →* (0, 2n+3, 0, D+2n+3, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2 * n + 3, 0, D + (2 * n + 3), 0⟩)
  · have h := c_to_b (2 * n + 3) 0 (D + (2 * n + 3))
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3a: R5+R1 × (n+1): (0, 2n+3, 0, D+2n+3, 0) →* (0, 1, 0, D+n+2, 2n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 0, D + n + 2, 2 * n + 2⟩)
  · have h := r5r1_pairs (n + 1) 1 (D + n + 2) 0
    rw [show 1 + 2 * (n + 1) = 2 * n + 3 from by ring,
        show D + n + 2 + (n + 1) = D + (2 * n + 3) from by ring,
        show 0 + 2 * (n + 1) = 2 * n + 2 from by ring] at h
    exact h
  -- Phase 3b: final R5: (0, 1, 0, D+n+2, 2n+2) →⁺ (1, 0, 0, D+n+1, 2n+4)
  rw [show D + n + 2 = (D + n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, 0, D + n + 1, 2 * n + 2 + 2⟩)
  · show fm ⟨0, 0 + 1, 0, (D + n + 1) + 1, 2 * n + 2⟩ = some ⟨0 + 1, 0, 0, D + n + 1, 2 * n + 2 + 2⟩
    simp [fm]
  -- Phase 4: R3+R2 × (2n+4): (1, 0, 0, D+n+1, 2n+4) →* (2n+5, 0, 0, D+n+1, 0)
  rw [show D + n + 1 = (D + n) + 1 from by ring,
      show 2 * n + 2 + 2 = 2 * n + 4 from by ring]
  have h := r3r2_loop (2 * n + 4) 0 (D + n)
  rw [show 0 + (2 * n + 4) + 1 = 2 * n + 5 from by ring,
      show (D + n) + 1 = D + n + 1 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, D⟩ ↦ ⟨2 * n + 3, 0, 0, D, 0⟩) ⟨0, 0⟩
  intro ⟨n, D⟩
  exact ⟨⟨n + 1, D + n + 1⟩, main_trans n D⟩

end Sz22_2003_unofficial_210
