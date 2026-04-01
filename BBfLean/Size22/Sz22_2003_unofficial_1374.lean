import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1374: [63/10, 5/231, 2/3, 121/2, 15/11]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1 -1 -1
 1 -1  0  0  0
-1  0  0  0  2
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1374

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: drain a into e
theorem r4_chain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by omega]
    step fm
    rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    exact ih a d (e + 2)

-- R5+R2 chain: interleave e and d into c
theorem r5r2_chain : ∀ k c d e, ⟨0, 0, c, d + k, e + 2 * k⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by omega,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm  -- R5
    step fm  -- R2
    rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    exact ih (c + 2) d e

-- R3 chain: drain b into a
theorem r3_chain : ∀ k a b d, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a + k, b, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by omega]
    step fm
    rw [show a + (k + 1) = (a + 1) + k from by omega]
    exact ih (a + 1) b d

-- R1+R3 chain
theorem r1r3_chain : ∀ k b c d, ⟨1, b, c + k, d, 0⟩ [fm]⊢* ⟨1, b + k, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by omega]
    step fm  -- R1
    step fm  -- R3
    rw [show b + (k + 1) = (b + 1) + k from by omega,
        show d + (k + 1) = (d + 1) + k from by omega]
    exact ih (b + 1) c (d + 1)

-- Main transition: (n+1, 0, 0, n, 0) →⁺ (2n+2, 0, 0, 2n+1, 0)
theorem main_trans (n : ℕ) : ⟨n + 1, 0, 0, n, 0⟩ [fm]⊢⁺ ⟨2 * n + 2, 0, 0, 2 * n + 1, 0⟩ := by
  -- Phase 1: R4 chain
  have h1 : ⟨n + 1, 0, 0, n, 0⟩ [fm]⊢* ⟨0, 0, 0, n, 2 * n + 2⟩ := by
    rw [show n + 1 = 0 + (n + 1) from by omega]
    apply stepStar_trans (r4_chain (n + 1) 0 n 0)
    rw [show 0 + 2 * (n + 1) = 2 * n + 2 from by ring]; finish
  -- Phase 2: R5+R2 chain
  have h2 : ⟨0, 0, 0, n, 2 * n + 2⟩ [fm]⊢* ⟨0, 0, 2 * n, 0, 2⟩ := by
    have h := r5r2_chain n 0 0 2
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * n = 2 * n + 2 from by ring] at h
    exact h
  -- Phase 3: middle steps
  have h3 : ⟨0, 0, 2 * n, 0, 2⟩ [fm]⊢* ⟨1, 0, 2 * n + 1, 0, 0⟩ := by
    step fm; step fm; step fm; step fm; step fm; finish
  -- Phase 4: R1+R3 chain + R1 + R3 chain
  have h4 : ⟨1, 0, 2 * n + 1, 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 2, 0, 0, 2 * n + 1, 0⟩ := by
    have hr := r1r3_chain (2 * n) 0 1 0
    simp only [Nat.zero_add] at hr
    rw [show 1 + 2 * n = 2 * n + 1 from by ring] at hr
    apply stepStar_stepPlus_stepPlus hr
    -- goal: (1, 2n, 1, 2n, 0) [fm]⊢⁺ (2n+2, 0, 0, 2n+1, 0)
    step fm
    -- goal: (0, 2n+2, 0, 2n+1, 0) [fm]⊢⁺ (2n+2, 0, 0, 2n+1, 0)
    have hr3 := r3_chain (2 * n + 2) 0 0 (2 * n + 1)
    simp only [Nat.zero_add] at hr3
    exact hr3
  exact stepStar_stepPlus_stepPlus (stepStar_trans h1 (stepStar_trans h2 h3)) h4

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, n, 0⟩) 0
  intro n; exists 2 * n + 1; exact main_trans n
