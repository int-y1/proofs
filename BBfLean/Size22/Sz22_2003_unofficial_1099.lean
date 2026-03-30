import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1099: [5/6, 3773/2, 4/245, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  3  1
 2  0 -1 -2  0
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1099

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+1⟩
  | ⟨a, b, c+1, d+2, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: move e to b.
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R5 step.
theorem r5_step : ⟨0, b, 0, d + 1, 0⟩ [fm]⊢* ⟨0, b, 1, d, 0⟩ := by
  step fm; finish

-- Interleaved R3+R1+R1 chain.
theorem interleave : ∀ k, ∀ b c d, ⟨0, b + 2 * k, c + 1, d + 2 * k, 0⟩ [fm]⊢* ⟨0, b, c + k + 1, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + 2 * (k + 1) = b + 2 * k + 2 from by ring,
        show d + 2 * (k + 1) = d + 2 * k + 2 from by ring]
    show ⟨0, b + 2 * k + 2, (c + 1), (d + 2 * k) + 2, 0⟩ [fm]⊢* _
    step fm
    show ⟨0 + 2, b + 2 * k + 2, c, d + 2 * k, 0⟩ [fm]⊢* _
    rw [show (0 : ℕ) + 2 = 1 + 1 from by ring,
        show b + 2 * k + 2 = (b + 2 * k + 1) + 1 from by ring]
    step fm
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih b (c + 1) d)
    ring_nf; finish

-- Tail: R3+R1+R2.
theorem tail : ⟨0, 1, n + 1, d + 2, 0⟩ [fm]⊢* ⟨0, 0, n + 1, d + 3, 1⟩ := by
  step fm; step fm; step fm; finish

-- Drain: R3+R2+R2 repeated.
theorem drain : ∀ k, ∀ c d e, ⟨0, 0, c + k, d + 2, e⟩ [fm]⊢* ⟨0, 0, c, d + 2 + 4 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 6 = (d + 4) + 2 from by ring]
    apply stepStar_trans (ih c (d + 4) (e + 2))
    ring_nf; finish

-- Combined: e_to_b + R5.
theorem e_to_b_r5 : ∀ e, ⟨0, 0, 0, d + 1, e⟩ [fm]⊢* ⟨0, e, 1, d, 0⟩ := by
  intro e
  rw [show (e : ℕ) = 0 + e from by ring]
  apply stepStar_trans (e_to_b e (b := 0) (d := d + 1) (e := 0))
  rw [show 0 + e = e from by ring]
  exact r5_step

-- Full transition from canonical n to canonical n+1.
-- Canonical state n: (0, 0, 0, n*n+3*n+3, 2*n+1).
theorem full_trans (n : ℕ) :
    ⟨0, 0, 0, n * n + 3 * n + 3, 2 * n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, n * n + 5 * n + 7, 2 * n + 3⟩ := by
  -- Phase 1+2: e_to_b + R5.
  rw [show n * n + 3 * n + 3 = (n * n + 3 * n + 2) + 1 from by ring]
  -- We need ⊢⁺. The e_to_b_r5 gives ⊢*. Use tail (3 steps) to get ⊢⁺.
  -- Compose: e_to_b_r5 (⊢*) then interleave (⊢*) then tail_plus (⊢⁺) then drain (⊢*).
  -- Actually, let's use a single R4 step first to get ⊢⁺.
  rw [show (2 * n + 1 : ℕ) = 2 * n + 0 + 1 from by ring]
  step fm
  -- Now we have ⊢⁺ and the remaining goal is ⊢*
  -- State: (0, 1, 0, (n²+3n+2)+1, 2n)
  -- Continue e_to_b for remaining 2n
  rw [show (2 * n : ℕ) = 0 + 2 * n from by ring]
  apply stepStar_trans (e_to_b (2 * n) (b := 1) (d := (n * n + 3 * n + 2) + 1) (e := 0))
  -- Now at (0, 2n+1, 0, (n²+3n+2)+1, 0). R5.
  rw [show 1 + 2 * n = 2 * n + 1 from by ring]
  apply stepStar_trans (r5_step (b := 2 * n + 1) (d := n * n + 3 * n + 2))
  -- Now at (0, 2n+1, 1, n²+3n+2, 0). Interleave.
  rw [show 2 * n + 1 = 1 + 2 * n from by ring,
      show n * n + 3 * n + 2 = (n * n + n + 2) + 2 * n from by ring]
  apply stepStar_trans (interleave n 1 0 (n * n + n + 2))
  -- Now at (0, 1, n+1, n²+n+2, 0). Tail.
  rw [show 0 + n + 1 = n + 1 from by ring,
      show n * n + n + 2 = (n * n + n) + 2 from by ring]
  apply stepStar_trans (tail (n := n) (d := n * n + n))
  -- Now at (0, 0, n+1, n²+n+3, 1). Drain.
  rw [show n + 1 = 0 + (n + 1) from by ring,
      show n * n + n + 3 = (n * n + n + 1) + 2 from by ring]
  apply stepStar_trans (drain (n + 1) 0 (n * n + n + 1) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n * n + 3 * n + 3, 2 * n + 1⟩) 0
  intro n; exists (n + 1)
  show ⟨0, 0, 0, n * n + 3 * n + 3, 2 * n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, (n + 1) * (n + 1) + 3 * (n + 1) + 3, 2 * (n + 1) + 1⟩
  rw [show (n + 1) * (n + 1) + 3 * (n + 1) + 3 = n * n + 5 * n + 7 from by ring,
      show 2 * (n + 1) + 1 = 2 * n + 3 from by ring]
  exact full_trans n

end Sz22_2003_unofficial_1099
