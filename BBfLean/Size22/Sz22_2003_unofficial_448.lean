import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #448: [28/15, 1/22, 21/2, 11/3, 50/77]

Vector representation:
```
 2 -1 -1  1  0
-1  0  0  0 -1
-1  1  0  1  0
 0 -1  0  0  1
 1  0  2 -1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_448

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

-- R3 chain: (a+k, b, 0, d, 0) ⊢* (a, b+k, 0, d+k, 0)
theorem r3_chain : ∀ k, ∀ a b d, ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+k, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R4 chain: (0, b+k, 0, d, e) ⊢* (0, b, 0, d, e+k)
theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b+k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R5+R2 chain: (0, 0, c, D+k+1, k+k+1) ⊢* (1, 0, c+k+k+2, D, 0)
theorem r5r2_chain : ∀ k, ∀ c D, ⟨0, 0, c, D+k+1, k+k+1⟩ [fm]⊢* ⟨1, 0, c+k+k+2, D, 0⟩ := by
  intro k; induction' k with k h <;> intro c D
  · step fm; ring_nf; finish
  rw [show (k + 1) + (k + 1) + 1 = (k + k + 1 + 1) + 1 from by ring,
      show D + (k + 1) + 1 = (D + k + 1) + 1 from by ring]
  step fm
  rw [show k + k + 1 + 1 = (k + k + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (h (c + 2) D)
  ring_nf; finish

-- R3+R1 interleaved chain: (a+1, 0, k, d, 0) ⊢* (a+k+1, 0, 0, d+2*k, 0)
theorem r3r1_chain : ∀ k, ∀ a d, ⟨a+1, 0, k, d, 0⟩ [fm]⊢* ⟨a+k+1, 0, 0, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  step fm
  step fm
  rw [show d + 1 + 1 = d + 2 from by ring,
      show a + 2 = (a + 1) + 1 from by ring]
  apply stepStar_trans (h (a + 1) (d + 2))
  ring_nf; finish

-- Remaining phases after first R3 step
theorem rest_trans (n d : ℕ) : ⟨2*n+2, 1, 0, d+1, 0⟩ [fm]⊢* ⟨2*n+5, 0, 0, d+5*n+9, 0⟩ := by
  have h1 := r3_chain (2*n+2) 0 1 (d+1)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 1 + (2 * n + 2) = 0 + (2 * n + 3) from by ring,
      show d + 1 + (2 * n + 2) = d + 2 * n + 3 from by ring]
  apply stepStar_trans (r4_chain (2*n+3) 0 (d+2*n+3) 0)
  rw [show (0 : ℕ) + (2 * n + 3) = (n + 1) + (n + 1) + 1 from by ring,
      show d + 2 * n + 3 = (d + n + 1) + (n + 1) + 1 from by ring]
  apply stepStar_trans (r5r2_chain (n+1) 0 (d+n+1))
  rw [show (0 : ℕ) + (n + 1) + (n + 1) + 2 = 2 * n + 4 from by ring]
  have h := r3r1_chain (2*n+4) 0 (d+n+1)
  simp only [Nat.zero_add] at h
  convert h using 2; ring_nf

-- Main transition
theorem main_trans (n d : ℕ) : ⟨2*n+3, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2*n+5, 0, 0, d+5*n+9, 0⟩ := by
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
  step fm
  exact rest_trans n d

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 4, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, d⟩ ↦ ⟨2*n+3, 0, 0, d, 0⟩) ⟨0, 4⟩
  intro ⟨n, d⟩
  exact ⟨⟨n+1, d+5*n+9⟩, main_trans n d⟩

end Sz22_2003_unofficial_448
