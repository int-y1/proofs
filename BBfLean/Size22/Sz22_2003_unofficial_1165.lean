import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1165: [5/6, 44/35, 91/2, 3/11, 66/13]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  0
-1  0  0  1  0  1
 0  1  0  0 -1  0
 1  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1165

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e+1, f⟩
  | _ => none

-- Phase 1: R3 repeated.
theorem r3_chain : ∀ k, ∀ a d f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (f + 1))
    ring_nf; finish

-- Phase 2: R4 repeated.
theorem r4_chain : ∀ k, ∀ b e, ⟨0, b, 0, d, e + k, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- Phase 3b: R1+R1+R2 chain.
theorem r1r1r2_chain : ∀ k, ∀ b c d e, ⟨2, b + 2 * k, c, d + k, e, f⟩ [fm]⊢* ⟨2, b, c + k, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) d (e + 1))
    ring_nf; finish

-- Phase 4: R3+R2 chain.
theorem r3r2_chain : ∀ k, ∀ a c e f, ⟨a + 1, 0, c + k, 0, e, f⟩ [fm]⊢* ⟨a + 1 + k, 0, c, 0, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1) (f + 1))
    ring_nf; finish

-- Full transition
theorem main_trans (n F : ℕ) : (⟨n + 1, 0, 0, 0, 2 * n, F⟩ : Q) [fm]⊢⁺
    ⟨n + 2, 0, 0, 0, 2 * n + 2, F + 2 * n⟩ := by
  -- Build each phase as a standalone have, then compose
  -- Phase 1: R3 x (n+1) steps
  have h1 : (⟨n + 1, 0, 0, 0, 2 * n, F⟩ : Q) [fm]⊢* ⟨0, 0, 0, n + 1, 2 * n, F + n + 1⟩ := by
    have := r3_chain (n + 1) 0 0 F (e := 2 * n)
    simp only [Nat.zero_add] at this
    convert this using 2
  -- Phase 2: R4 x 2n steps
  have h2 : (⟨0, 0, 0, n + 1, 2 * n, F + n + 1⟩ : Q) [fm]⊢* ⟨0, 2 * n, 0, n + 1, 0, F + n + 1⟩ := by
    have := r4_chain (2 * n) 0 0 (d := n + 1) (f := F + n + 1)
    simp only [Nat.zero_add] at this
    exact this
  -- Phase 3b: R1+R1+R2 x n rounds
  have h3b : (⟨2, 2 * n, 0, n, 2, F + n⟩ : Q) [fm]⊢* ⟨2, 0, n, 0, n + 2, F + n⟩ := by
    have := r1r1r2_chain n 0 0 0 2 (f := F + n)
    simp only [Nat.zero_add] at this
    rw [show 2 + n = n + 2 from by ring] at this
    exact this
  -- Phase 4: R3+R2 x n pairs
  have h4 : (⟨2, 0, n, 0, n + 2, F + n⟩ : Q) [fm]⊢* ⟨n + 2, 0, 0, 0, 2 * n + 2, F + 2 * n⟩ := by
    have := r3r2_chain n 1 0 (n + 2) (F + n)
    simp only [Nat.zero_add] at this
    rw [show 1 + 1 + n = n + 2 from by ring,
        show n + 2 + n = 2 * n + 2 from by ring,
        show F + n + n = F + 2 * n from by ring] at this
    convert this using 2
  -- Compose all: ⊢* + ⊢* + ⊢* + ⊢* + ⊢* = ⊢*
  -- Need at least one step for ⊢⁺. Phase 3a has 3 steps.
  -- Actually we need ⊢⁺. Use stepStar_stepPlus via the first R3 step.
  apply stepStar_stepPlus_stepPlus h1
  apply stepStar_stepPlus_stepPlus h2
  have h3a' : (⟨0, 2 * n, 0, n + 1, 0, F + n + 1⟩ : Q) [fm]⊢⁺ ⟨2, 2 * n, 0, n, 2, F + n⟩ := by
    rw [show F + n + 1 = (F + n) + 1 from by ring]
    step fm; step fm; step fm; finish
  exact stepPlus_stepStar_stepPlus
    (stepPlus_stepStar_stepPlus h3a' h3b) h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, F⟩ ↦ ⟨n + 1, 0, 0, 0, 2 * n, F⟩) ⟨0, 0⟩
  intro ⟨n, F⟩; exists ⟨n + 1, F + 2 * n⟩
  show (⟨n + 1, 0, 0, 0, 2 * n, F⟩ : Q) [fm]⊢⁺ ⟨n + 1 + 1, 0, 0, 0, 2 * (n + 1), F + 2 * n⟩
  rw [show n + 1 + 1 = n + 2 from by ring, show 2 * (n + 1) = 2 * n + 2 from by ring]
  exact main_trans n F

end Sz22_2003_unofficial_1165
