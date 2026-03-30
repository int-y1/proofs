import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #764: [35/6, 4/55, 9317/2, 3/7, 5/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  1  3
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_764

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R3 drain: (a+k, 0, 0, d, e) →* (a, 0, 0, d+k, e+3*k)
theorem r3_drain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 3))
    ring_nf; finish

-- R4 drain: (0, b, 0, k, e) →* (0, b+k, 0, 0, e)
theorem r4_drain : ∀ k b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- R1R1R2 chain: (2, 2*k, c, d, e+k) →* (2, 0, c+k, d+2*k, e)
theorem r1r1r2_chain : ∀ k c d e, ⟨2, 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, 0, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

-- R2 drain: (a, 0, c+k, d, e+k) →* (a+2*k, 0, c, d, e)
theorem r2_drain : ∀ k a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

-- Main transition: (n+3, 0, 0, n+1, n) →⁺ (2*n+6, 0, 0, 2*n+4, 2*n+3)
theorem main_trans (n : ℕ) : ⟨n + 3, 0, 0, n + 1, n⟩ [fm]⊢⁺ ⟨2 * n + 6, 0, 0, 2 * n + 4, 2 * n + 3⟩ := by
  -- First R3 step (gives ⊢⁺)
  rw [show n + 3 = (n + 2) + 1 from by ring]
  step fm
  -- Now at (n+2, 0, 0, n+1+1, n+3). R3 drain remaining.
  have h := r3_drain (n + 2) 0 (n + 1 + 1) (n + 3)
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  rw [show n + 1 + 1 + (n + 2) = 2 * n + 4 from by ring,
      show n + 3 + 3 * (n + 2) = 4 * n + 9 from by ring]
  -- R4 drain
  apply stepStar_trans (r4_drain (2 * n + 4) 0 (4 * n + 9))
  simp only [Nat.zero_add]
  -- R5 + R2
  rw [show (4 * n + 9 : ℕ) = (4 * n + 7) + 1 + 1 from by ring]
  step fm  -- R5
  step fm  -- R2
  -- R1R1R2 chain
  rw [show (2 * n + 4 : ℕ) = 2 * (n + 2) from by ring,
      show (4 * n + 7 : ℕ) = (3 * n + 5) + (n + 2) from by ring]
  apply stepStar_trans (r1r1r2_chain (n + 2) 0 0 (3 * n + 5))
  simp only [Nat.zero_add]
  -- R2 drain
  rw [show (n + 2 : ℕ) = 0 + (n + 2) from by ring,
      show (3 * n + 5 : ℕ) = (2 * n + 3) + (n + 2) from by ring]
  have h2 := r2_drain (n + 2) 2 0 (2 * (n + 2)) (2 * n + 3)
  simp only [Nat.zero_add] at h2 ⊢
  apply stepStar_trans h2
  rw [show 2 + 2 * (n + 2) = 2 * n + 6 from by ring,
      show 2 * (n + 2) = 2 * n + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 3, 0, 0, n + 1, n⟩) 0
  intro n; exists 2 * n + 3
  exact main_trans n
