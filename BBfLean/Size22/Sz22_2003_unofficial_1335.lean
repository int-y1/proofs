import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1335: [63/10, 2/33, 1331/2, 5/7, 21/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  3
 0  0  1 -1  0
 0  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1335

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3 chain: drain a, each step adds 3 to e.
theorem r3_chain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ d _)
    ring_nf; finish

-- R4 chain: drain d, each step adds 1 to c.
theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R2+R1 interleaved spiral.
theorem r2r1_spiral : ∀ k j E, ⟨0, j + 1, k, j + 1, E + k⟩ [fm]⊢* ⟨0, j + 1 + k, 0, j + 1 + k, E⟩ := by
  intro k; induction' k with k ih <;> intro j E
  · exists 0
  · rw [show E + (k + 1) = (E + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R2 drain.
theorem r2_drain : ∀ k a b d e, ⟨a, b + k, 0, d, e + k⟩ [fm]⊢* ⟨a + k, b, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- Main transition: (n+2, 0, 0, n+2, e) ⊢⁺ (n+3, 0, 0, n+3, e+n)
theorem main_trans : ⟨n + 2, 0, 0, n + 2, e⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, n + 3, e + n⟩ := by
  -- Phase 1: first R3 step
  step fm
  -- Phase 1 continued: remaining R3 chain
  show ⟨n + 1, 0, 0, n + 2, e + 3⟩ [fm]⊢* ⟨n + 3, 0, 0, n + 3, e + n⟩
  rw [show (n + 1 : ℕ) = 0 + (n + 1) from by ring]
  apply stepStar_trans (r3_chain (n + 1) 0 (n + 2) (e + 3))
  rw [show e + 3 + 3 * (n + 1) = e + 3 * n + 6 from by ring]
  -- Phase 2: R4 chain
  rw [show (n + 2 : ℕ) = 0 + (n + 2) from by ring]
  apply stepStar_trans (r4_chain (n + 2) 0 0 (e + 3 * n + 6))
  rw [show (0 : ℕ) + (n + 2) = n + 2 from by ring]
  -- Phase 3: R5 step
  rw [show e + 3 * n + 6 = (e + 3 * n + 5) + 1 from by ring]
  step fm
  -- Phase 4: R2+R1 spiral
  rw [show e + 3 * n + 5 = (e + 2 * n + 3) + (n + 2) from by ring]
  apply stepStar_trans (r2r1_spiral (n + 2) 0 (e + 2 * n + 3))
  rw [show 0 + 1 + (n + 2) = n + 3 from by ring]
  -- Phase 5: R2 drain
  rw [show (n + 3 : ℕ) = 0 + (n + 3) from by ring,
      show e + 2 * n + 3 = (e + n) + (n + 3) from by ring]
  apply stepStar_trans (r2_drain (n + 3) 0 0 (0 + (n + 3)) (e + n))
  rw [show 0 + (n + 3) = n + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨n + 2, 0, 0, n + 2, e⟩) ⟨0, 0⟩
  intro ⟨n, e⟩
  exact ⟨⟨n + 1, e + n⟩, main_trans⟩

end Sz22_2003_unofficial_1335
