import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1923: [9/70, 2/33, 605/2, 49/11, 2/7]

Vector representation:
```
-1  2 -1 -1  0
 1 -1  0  0 -1
-1  0  1  0  2
 0  0  0  2 -1
 1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1923

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R3 drain: (k, 0, c, 0, e) →* (0, 0, c+k, 0, e+2*k)
theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · simp; exists 0
  rw [show k + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih (c + 1) (e + 2))
  ring_nf; finish

-- R4 chain: (0, 0, c, d, e+k) →* (0, 0, c, d+2*k, e)
theorem r4_chain : ∀ k, ∀ c d e,
    ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  rw [show e + (k + 1) = e + k + 1 from by ring]
  step fm
  apply stepStar_trans (ih c (d + 2) e)
  ring_nf; finish

-- R5+R1 pairs: (0, b, k+1, 2*k+d+2, 0) →* (0, b+2*k+2, 0, d, 0)
theorem r5r1_chain : ∀ k, ∀ b d,
    ⟨0, b, k + 1, 2 * k + d + 2, 0⟩ [fm]⊢* ⟨0, b + 2 * k + 2, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · simp
    rw [show d + 2 = d + 1 + 1 from by ring]
    step fm; step fm; finish
  · rw [show 2 * (k + 1) + d + 2 = (2 * k + d + 2) + 1 + 1 from by ring,
        show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + d + 2 + 1 = (2 * k + d + 2) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d)
    ring_nf; finish

-- Tail: (0, b+1, 0, 2, 0) → (1, b+1, 0, 0, 0) in 5 steps
theorem tail : ∀ b, ⟨0, b + 1, 0, 2, 0⟩ [fm]⊢* ⟨1, b + 1, 0, 0, 0⟩ := by
  intro b
  step fm; step fm; step fm; step fm; step fm; finish

-- Drain: (k+1, b+2*(j+1), k, 0, 0) →* (k+j+2, b, k+j+1, 0, 0)
theorem drain : ∀ j, ∀ k b,
    ⟨k + 1, b + 2 * (j + 1), k, 0, 0⟩ [fm]⊢* ⟨k + j + 2, b, k + j + 1, 0, 0⟩ := by
  intro j; induction' j with j ih <;> intro k b
  · step fm; step fm; step fm; finish
  · rw [show b + 2 * (j + 1 + 1) = (b + 2 * (j + 1)) + 2 from by ring]
    step fm
    step fm
    step fm
    rw [show k + 2 = (k + 1) + 1 from by ring]
    apply stepStar_trans (ih (k + 1) b)
    ring_nf; finish

-- Main transition: (n+1, 0, n, 0, 0) →⁺ (2n+2, 0, 2n+1, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, n, 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 2, 0, 2 * n + 1, 0, 0⟩ := by
  -- Phase 1: R3 drain
  -- (n+1, 0, n, 0, 0) →R3→ (n, 0, n+1, 0, 2) →* (0, 0, 2n+1, 0, 2n+2)
  step fm
  apply stepStar_trans (r3_drain n (n + 1) 2)
  -- now at (0, 0, n+1+n, 0, 2+2*n)
  -- Phase 2: R4 chain
  rw [show (2 + 2 * n : ℕ) = 0 + (2 + 2 * n) from by ring]
  apply stepStar_trans (r4_chain (2 + 2 * n) (n + 1 + n) 0 0)
  -- now at (0, 0, n+1+n, 0+2*(2+2*n), 0)
  -- Phase 3: R5+R1 chain
  rw [show n + 1 + n = 2 * n + 1 from by ring,
      show (0 + 2 * (2 + 2 * n) : ℕ) = 2 * (2 * n) + 2 + 2 from by ring,
      show 2 * n + 1 = 2 * n + 1 from rfl]
  apply stepStar_trans (r5r1_chain (2 * n) 0 2)
  -- now at (0, 0+2*(2*n)+2, 0, 2, 0) = (0, 4n+2, 0, 2, 0)
  -- Phase 4: tail
  rw [show 0 + 2 * (2 * n) + 2 = (4 * n + 1) + 1 from by ring]
  apply stepStar_trans (tail (4 * n + 1))
  -- now at (1, 4n+2, 0, 0, 0)
  -- Phase 5: drain
  rw [show (4 * n + 1 + 1 : ℕ) = 0 + 2 * (2 * n + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (drain (2 * n) 0 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 13)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, n + 1, 0, 0⟩) 0
  intro n
  refine ⟨2 * n + 2, ?_⟩
  show ⟨n + 2, 0, n + 1, 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 2 + 2, 0, 2 * n + 2 + 1, 0, 0⟩
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show 2 * n + 2 + 2 = 2 * (n + 1) + 2 from by ring,
      show 2 * n + 2 + 1 = 2 * (n + 1) + 1 from by ring]
  exact main_trans (n + 1)
