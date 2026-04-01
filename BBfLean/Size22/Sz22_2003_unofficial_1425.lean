import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1425: [7/15, 2/3, 99/14, 5/11, 231/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  0
-1  2  0 -1  1
 0  0  1  0 -1
-1  1  0  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1425

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
  | _ => none

-- R4 chain: move e to c
theorem e_to_c : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

-- Spiral inner: (R1, R1, R3) repeated k times
theorem spiral_inner : ∀ k, ∀ a c d e, ⟨a + k, 2, c + 2 * k, d, e⟩ [fm]⊢* ⟨a, 2, c, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show a + (k + 1) = (a + 1) + k from by ring]
    apply stepStar_trans (ih (a + 1) (c + 2) d e)
    step fm; step fm; step fm
    ring_nf; finish

-- Drain: (R3, R2, R2) repeated k times
theorem drain : ∀ k, ∀ a d e, ⟨a + 1, 0, 0, d + k, e⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) d (e + 1))
    ring_nf; finish

-- Phase 2: from (n+2, 0, 2*n+2, 0, 0) ⊢⁺ (n+3, 0, 0, 0, 2*n+4)
theorem phase2 : ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
  -- R5, R1, R3
  step fm; step fm; step fm
  -- (n, 2, Nat.add 0 (2*n+1), 1, 2) ⊢* (n+3, 0, 0, 0, 2*n+4)
  change ⟨n, 2, 2 * n + 1, 1, 2⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 2 * n + 4⟩
  -- spiral_inner: need n = 0 + n and 2*n+1 = 1 + 2*n, but only in specific positions
  -- Use have with spiral_inner, then massage the result
  have h1 := spiral_inner n 0 1 1 2
  -- h1 : (0 + n, 2, 1 + 2 * n, 1, 2) ⊢* (0, 2, 1, 1 + n, 2 + n)
  simp only [Nat.zero_add] at h1
  -- h1 : (n, 2, 1 + 2 * n, 1, 2) ⊢* (0, 2, 1, 1 + n, 2 + n)
  rw [show 2 * n + 1 = 1 + 2 * n from by ring]
  apply stepStar_trans h1
  -- (0, 2, 1, 1+n, 2+n) ⊢* (n+3, 0, 0, 0, 2*n+4)
  -- R1, R2
  step fm; step fm
  -- (1, 0, 0, 1+n+1, 2+n) ⊢* ...
  -- drain: need (1, 0, 0, n+2, n+2) → ...
  have h2 := drain (n + 2) 0 0 (n + 2)
  -- h2 : (0 + 1, 0, 0, 0 + (n + 2), n + 2) ⊢* (0 + 1 + (n + 2), 0, 0, 0, n + 2 + (n + 2))
  simp only [Nat.zero_add] at h2
  rw [show 1 + n + 1 = n + 2 from by ring,
      show (2 + n : ℕ) = n + 2 from by ring]
  apply stepStar_trans h2
  ring_nf; finish

-- Main transition
theorem main_trans : ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
  have h := e_to_c (2 * n + 2) (n + 2) 0 0
  -- h : (n+2, 0, 0, 0, 0 + (2*n+2)) ⊢* (n+2, 0, 0+(2*n+2), 0, 0)
  simp only [Nat.zero_add] at h
  -- h : (n+2, 0, 0, 0, 2*n+2) ⊢* (n+2, 0, 2*n+2, 0, 0)
  exact stepStar_stepPlus_stepPlus h phase2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩) 0
  intro n; exists n + 1; exact main_trans
